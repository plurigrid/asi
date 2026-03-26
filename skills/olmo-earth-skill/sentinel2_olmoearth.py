#!/usr/bin/env python3
"""
Sentinel-2 + OlmoEarth Embedding Pipeline

Downloads Sentinel-2 L2A imagery from Microsoft Planetary Computer,
runs OlmoEarth inference, and writes embeddings in the zig-syrup
WholeEarthModel binary format.

Usage:
    python sentinel2_olmoearth.py \
        --lat 37.77 --lon -122.42 \
        --size 0.1 \
        --start 2024-07-01 --end 2024-08-31 \
        --max-cloud 10 \
        --model base \
        --output /tmp/embeddings.bin

    python sentinel2_olmoearth.py --diff /tmp/q1.bin /tmp/q3.bin

Requirements:
    pip install olmoearth-pretrain torch planetary-computer pystac-client rasterio numpy
"""

import argparse
import struct
import sys
from pathlib import Path

import numpy as np

# --------------------------------------------------------------------------
# Binary format for zig-syrup EmbeddingLoader.loadFromFile()
#
#   [u32 tile_count] [u16 embed_dim] [f32 * D * N] [f64 lat, f64 lon * N]
#
# All little-endian.
# --------------------------------------------------------------------------

def write_embeddings_bin(path: str, embeddings: np.ndarray, coords: np.ndarray):
    """
    Write embeddings + coordinates in zig-syrup binary format.

    Args:
        path: Output file path
        embeddings: (N, D) float32 array
        coords: (N, 2) float64 array of (lat, lon)
    """
    n, d = embeddings.shape
    with open(path, "wb") as f:
        f.write(struct.pack("<I", n))       # u32 tile_count
        f.write(struct.pack("<H", d))       # u16 embed_dim
        f.write(embeddings.astype("<f4").tobytes())  # f32 embeddings
        f.write(coords.astype("<f8").tobytes())      # f64 lat/lon pairs


def read_embeddings_bin(path: str):
    """Read embeddings from zig-syrup binary format."""
    with open(path, "rb") as f:
        tile_count = struct.unpack("<I", f.read(4))[0]
        embed_dim = struct.unpack("<H", f.read(2))[0]
        emb_bytes = f.read(4 * tile_count * embed_dim)
        embeddings = np.frombuffer(emb_bytes, dtype="<f4").reshape(tile_count, embed_dim)
        coord_bytes = f.read(16 * tile_count)
        coords = np.frombuffer(coord_bytes, dtype="<f8").reshape(tile_count, 2)
    return embeddings, coords


# --------------------------------------------------------------------------
# Sentinel-2 download via Microsoft Planetary Computer
# --------------------------------------------------------------------------

def search_sentinel2(lat: float, lon: float, size: float,
                     start: str, end: str, max_cloud: float):
    """
    Search Planetary Computer for Sentinel-2 L2A scenes.

    Args:
        lat, lon: Center coordinate
        size: Bounding box half-width in degrees
        start, end: Date range (YYYY-MM-DD)
        max_cloud: Maximum cloud cover percentage

    Returns:
        Best (least cloudy) STAC item, or None
    """
    import planetary_computer as pc
    import pystac_client

    catalog = pystac_client.Client.open(
        "https://planetarycomputer.microsoft.com/api/stac/v1",
        modifier=pc.sign_inplace,
    )

    bbox = [lon - size, lat - size, lon + size, lat + size]

    search = catalog.search(
        collections=["sentinel-2-l2a"],
        bbox=bbox,
        datetime=f"{start}/{end}",
        query={"eo:cloud_cover": {"lt": max_cloud}},
    )

    items = list(search.items())
    if not items:
        return None

    # Pick the least cloudy scene
    best = min(items, key=lambda x: x.properties.get("eo:cloud_cover", 100))
    return best


def download_bands(item, crop_size: int = 512) -> tuple:
    """
    Download all 12 OlmoEarth Sentinel-2 bands from a STAC item.

    Returns:
        image: (C, H, W) int32 array, 12 bands
        crs: coordinate reference system
        transform: affine transform
        datetime: acquisition datetime
    """
    import rasterio
    from rasterio.vrt import WarpedVRT
    from rasterio.enums import Resampling

    # OlmoEarth band order for Sentinel-2 L2A
    band_order = [
        "B02", "B03", "B04", "B08",          # 10m
        "B05", "B06", "B07", "B8A", "B11", "B12",  # 20m
        "B01", "B09",                          # 60m
    ]

    # Use B02 (10m) as the reference grid
    with rasterio.open(item.assets["B02"].href) as ref_src:
        ref_crs = ref_src.crs
        ref_transform = ref_src.transform
        ref_width = ref_src.width
        ref_height = ref_src.height

    crop_h = min(crop_size, ref_height)
    crop_w = min(crop_size, ref_width)

    image = np.zeros((len(band_order), crop_h, crop_w), dtype=np.int32)

    for i, band_name in enumerate(band_order):
        href = item.assets[band_name].href
        with rasterio.open(href) as src:
            with WarpedVRT(
                src,
                crs=ref_crs,
                transform=ref_transform,
                width=crop_w,
                height=crop_h,
                resampling=Resampling.bilinear,
            ) as vrt:
                image[i, :, :] = vrt.read(1)

    return image, ref_crs, ref_transform, item.datetime


# --------------------------------------------------------------------------
# OlmoEarth inference
# --------------------------------------------------------------------------

def compute_embeddings(image: np.ndarray, dt, model_size: str = "base",
                       patch_size: int = 64) -> tuple:
    """
    Run OlmoEarth encoder on a Sentinel-2 image.

    Args:
        image: (C, H, W) int32 array, 12 bands
        dt: datetime of acquisition
        model_size: one of "nano", "tiny", "base", "large"
        patch_size: spatial crop size for inference (default 64)

    Returns:
        embeddings: (N, D) float32 array
        grid_coords: (N, 2) float64 array of relative (row, col) positions
    """
    import torch
    from olmoearth_pretrain.model_loader import ModelID, load_model_from_id
    from olmoearth_pretrain.datatypes import MaskedOlmoEarthSample, MaskValue
    from olmoearth_pretrain.data.constants import Modality
    from olmoearth_pretrain.data.normalize import Normalizer, Strategy

    model_ids = {
        "nano": ModelID.OLMOEARTH_V1_NANO,
        "tiny": ModelID.OLMOEARTH_V1_TINY,
        "base": ModelID.OLMOEARTH_V1_BASE,
        "large": ModelID.OLMOEARTH_V1_LARGE,
    }

    model_id = model_ids[model_size]
    model = load_model_from_id(model_id)
    device = torch.device("cuda" if torch.cuda.is_available() else
                          "mps" if torch.backends.mps.is_available() else "cpu")
    model.to(device)
    model.eval()

    # Rearrange (C, H, W) -> (1, H, W, 1, C) for OlmoEarth
    img = image.transpose(1, 2, 0)[None, :, :, None, :]  # (1, H, W, 1, 12)

    # Normalize
    normalizer = Normalizer(Strategy.COMPUTED)
    img = normalizer.normalize(Modality.SENTINEL2_L2A, img)

    # Timestamp: (day, month_0indexed, year)
    day = dt.day
    month_0idx = dt.month - 1
    year = dt.year

    _, h, w, _, _ = img.shape
    embeddings_list = []
    grid_positions = []

    for y in range(0, h - patch_size + 1, patch_size):
        for x in range(0, w - patch_size + 1, patch_size):
            crop = img[:, y:y + patch_size, x:x + patch_size, :, :]

            sample = MaskedOlmoEarthSample(
                sentinel2_l2a=torch.tensor(
                    crop, dtype=torch.float32, device=device
                ),
                sentinel2_l2a_mask=torch.ones(
                    (1, patch_size, patch_size, 1, 3),
                    dtype=torch.float32, device=device,
                ) * MaskValue.ONLINE_ENCODER.value,
                timestamps=torch.tensor(
                    [day, month_0idx, year], device=device
                )[None, None, :],
            )

            with torch.no_grad():
                output = model.encoder(
                    sample, fast_pass=True, patch_size=4
                )
                tokens = output["tokens_and_masks"]
                feat = tokens.sentinel2_l2a  # (1, H', W', T, S, D)
                # Pool over time (T) and band-set (S) dims
                pooled = feat.mean(dim=[3, 4])  # (1, H', W', D)
                # Spatial average to get a single vector per patch
                embedding = pooled.mean(dim=[1, 2])  # (1, D)
                embeddings_list.append(embedding.cpu().numpy())

            # Relative center of this patch in the image
            cy = (y + patch_size / 2) / h
            cx = (x + patch_size / 2) / w
            grid_positions.append([cy, cx])

    embeddings = np.concatenate(embeddings_list, axis=0)  # (N, D)
    grid_positions = np.array(grid_positions, dtype=np.float64)

    print(f"  Computed {embeddings.shape[0]} embeddings, dim={embeddings.shape[1]}")
    return embeddings, grid_positions


def grid_to_geo_coords(grid_positions: np.ndarray, crs, transform,
                        image_h: int, image_w: int,
                        center_lat: float, center_lon: float) -> np.ndarray:
    """
    Convert relative grid positions to geographic lat/lon.

    For simplicity, we use an affine approximation from the center coordinate
    and image extent. For production use, pyproj reprojection from the UTM CRS
    would be more accurate.
    """
    # Each pixel is ~10m, so image extent in degrees is approximately:
    # 10m * pixels / 111320 m/deg (at equator, longitude adjusted by cos(lat))
    import math
    lat_extent = (image_h * 10.0) / 111320.0
    lon_extent = (image_w * 10.0) / (111320.0 * math.cos(math.radians(center_lat)))

    coords = np.zeros((len(grid_positions), 2), dtype=np.float64)
    for i, (ry, rx) in enumerate(grid_positions):
        coords[i, 0] = center_lat + (0.5 - ry) * lat_extent   # lat
        coords[i, 1] = center_lon + (rx - 0.5) * lon_extent    # lon

    return coords


# --------------------------------------------------------------------------
# Diff tool
# --------------------------------------------------------------------------

def diff_embeddings(path_a: str, path_b: str):
    """Compare two embedding files by cosine similarity."""
    emb_a, coords_a = read_embeddings_bin(path_a)
    emb_b, coords_b = read_embeddings_bin(path_b)

    print(f"File A: {path_a} — {emb_a.shape[0]} tiles, dim={emb_a.shape[1]}")
    print(f"File B: {path_b} — {emb_b.shape[0]} tiles, dim={emb_b.shape[1]}")

    if emb_a.shape != emb_b.shape:
        print("Warning: different shapes, comparing min(N_a, N_b) tiles")

    n = min(len(emb_a), len(emb_b))

    # Cosine similarity per tile
    dot = np.sum(emb_a[:n] * emb_b[:n], axis=1)
    norm_a = np.linalg.norm(emb_a[:n], axis=1)
    norm_b = np.linalg.norm(emb_b[:n], axis=1)
    cos_sim = dot / (norm_a * norm_b + 1e-8)

    print(f"\nCosine similarity ({n} tiles):")
    print(f"  Mean:   {cos_sim.mean():.4f}")
    print(f"  Median: {np.median(cos_sim):.4f}")
    print(f"  Min:    {cos_sim.min():.4f} (tile {cos_sim.argmin()})")
    print(f"  Max:    {cos_sim.max():.4f}")
    print(f"  Std:    {cos_sim.std():.4f}")

    # Show the tiles with most change
    most_changed = np.argsort(cos_sim)[:5]
    print(f"\nMost changed tiles (lowest cosine similarity):")
    for idx in most_changed:
        lat, lon = coords_a[idx]
        print(f"  Tile {idx}: cos={cos_sim[idx]:.4f} at ({lat:.4f}, {lon:.4f})")


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Sentinel-2 + OlmoEarth embedding pipeline"
    )
    sub = parser.add_subparsers(dest="command")

    # Default: compute embeddings
    parser.add_argument("--lat", type=float, help="Center latitude")
    parser.add_argument("--lon", type=float, help="Center longitude")
    parser.add_argument("--size", type=float, default=0.1,
                        help="Bbox half-width in degrees (default: 0.1)")
    parser.add_argument("--start", type=str, help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", type=str, help="End date (YYYY-MM-DD)")
    parser.add_argument("--max-cloud", type=float, default=15,
                        help="Max cloud cover %% (default: 15)")
    parser.add_argument("--model", type=str, default="base",
                        choices=["nano", "tiny", "base", "large"],
                        help="OlmoEarth model size (default: base)")
    parser.add_argument("--crop", type=int, default=512,
                        help="Image crop size in pixels (default: 512)")
    parser.add_argument("--output", type=str, default="/tmp/olmoearth_embeddings.bin",
                        help="Output .bin file path")
    parser.add_argument("--diff", nargs=2, metavar=("FILE_A", "FILE_B"),
                        help="Compare two embedding files")

    args = parser.parse_args()

    if args.diff:
        diff_embeddings(args.diff[0], args.diff[1])
        return

    if not all([args.lat, args.lon, args.start, args.end]):
        parser.print_help()
        print("\nError: --lat, --lon, --start, --end are required")
        sys.exit(1)

    print(f"Searching Sentinel-2 L2A: center=({args.lat}, {args.lon}), "
          f"size={args.size}°, {args.start} to {args.end}, cloud<{args.max_cloud}%")

    item = search_sentinel2(
        args.lat, args.lon, args.size,
        args.start, args.end, args.max_cloud,
    )

    if item is None:
        print("No Sentinel-2 scenes found matching criteria. Try:")
        print("  - Widening the date range")
        print("  - Increasing --max-cloud")
        print("  - Checking the coordinates are over land")
        sys.exit(1)

    cloud = item.properties.get("eo:cloud_cover", "?")
    print(f"Selected scene: {item.id}")
    print(f"  Date: {item.datetime}")
    print(f"  Cloud cover: {cloud}%")

    print(f"Downloading 12 bands (crop={args.crop}px)...")
    image, crs, transform, dt = download_bands(item, crop_size=args.crop)
    print(f"  Image shape: {image.shape} (C, H, W)")

    print(f"Running OlmoEarth {args.model} encoder...")
    embeddings, grid_positions = compute_embeddings(
        image, dt, model_size=args.model
    )

    # Convert grid positions to geographic coordinates
    coords = grid_to_geo_coords(
        grid_positions, crs, transform,
        image.shape[1], image.shape[2],
        args.lat, args.lon,
    )

    print(f"Writing {embeddings.shape[0]} embeddings to {args.output}")
    write_embeddings_bin(args.output, embeddings, coords)

    # Verify
    emb_check, coord_check = read_embeddings_bin(args.output)
    assert emb_check.shape == embeddings.shape
    assert coord_check.shape == coords.shape
    file_size = Path(args.output).stat().st_size
    print(f"  File size: {file_size:,} bytes")
    print(f"  Tiles: {emb_check.shape[0]}, Dim: {emb_check.shape[1]}")
    print("Done.")


if __name__ == "__main__":
    main()
