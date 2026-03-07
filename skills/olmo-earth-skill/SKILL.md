---
name: olmo-earth-skill
description: "Whole Earth Model: Sentinel-2 satellite imagery to OlmoEarth embeddings on geodesic tiles, serialized via zig-syrup"
version: 1.0.0
trit: 1
trit_label: PLUS
---

# Whole Earth Model: Sentinel-2 + OlmoEarth + Zig-Syrup

**Trit**: +1 (PLUS — world creation via planetary observation)

## What This Does

Downloads real Sentinel-2 satellite imagery from Microsoft Planetary Computer,
runs AI2's OlmoEarth foundation model to produce per-tile embeddings, and writes
them into the zig-syrup WholeEarthModel binary format for high-speed serialization
and distributed sync over OCapN/CapTP.

```
Planetary Computer (free Sentinel-2 COGs)
    │
    ▼
Download 12-band L2A tiles (10-60m resolution)
    │
    ▼
OlmoEarth FlexiVit Encoder (768-dim Base model)
    │
    ▼
Per-tile embeddings as f32 vectors
    │
    ▼
Binary file → Zig EmbeddingLoader → WholeEarthModel.setEmbedding()
    │
    ▼
Syrup serialization → CapTP exchange at ~400 Hz
```

## Prerequisites

```bash
# Python dependencies (use uv for isolation)
pip install olmoearth-pretrain torch planetary-computer pystac-client rasterio numpy

# Zig (for the WholeEarthModel consumer)
# Already available in the flox environment
```

## Usage

### 1. Download + Embed a region

```bash
# Compute embeddings for the SF Bay Area, July 2024
python /Users/alice/.claude/skills/olmo-earth-skill/sentinel2_olmoearth.py \
    --lat 37.77 --lon -122.42 \
    --size 0.1 \
    --start 2024-07-01 --end 2024-08-31 \
    --max-cloud 10 \
    --model base \
    --output /tmp/sf_bay_embeddings.bin

# Compute for multiple locations
python /Users/alice/.claude/skills/olmo-earth-skill/sentinel2_olmoearth.py \
    --lat 51.51 --lon -0.13 \
    --size 0.2 \
    --start 2024-06-01 --end 2024-09-30 \
    --model tiny \
    --output /tmp/london_embeddings.bin
```

### 2. Load into zig-syrup WholeEarthModel

```zig
const bridge = @import("olmoearth_bridge");
const earth = @import("whole_earth");

// Build the geodesic mesh
var model = try earth.WholeEarthModel.init(allocator, .level_3, 768);
defer model.deinit();

// Load embeddings from the Python pipeline output
var loader = bridge.EmbeddingLoader.init(allocator, .base);
var embeddings = try loader.loadFromFile("/tmp/sf_bay_embeddings.bin");
defer embeddings.deinit();

// Map embeddings to nearest tiles
for (0..embeddings.tile_count) |i| {
    if (embeddings.getEmbedding(@intCast(i))) |emb| {
        const tile_id = model.tileAt(lat, lon) orelse continue;
        try model.setEmbedding(tile_id, emb);
    }
}

// Classify by impact zone
model.classifyByTrit(struct {
    fn classify(tile: *const earth.EarthTile) earth.Trit {
        if (bridge.classifyImpactZone(tile.center_lat, tile.center_lon)) |result| {
            return result.zone.zone_type.toTrit();
        }
        return .ergodic;
    }
}.classify);

// Serialize for CapTP exchange
const syrup_val = try model.toSyrup(allocator);
```

### 3. Compare tile embeddings over time

```bash
# Download two time windows
python sentinel2_olmoearth.py --lat 37.77 --lon -122.42 \
    --start 2024-01-01 --end 2024-03-31 --output /tmp/sf_q1.bin

python sentinel2_olmoearth.py --lat 37.77 --lon -122.42 \
    --start 2024-07-01 --end 2024-09-30 --output /tmp/sf_q3.bin

# Compare with the diff tool
python sentinel2_olmoearth.py --diff /tmp/sf_q1.bin /tmp/sf_q3.bin
```

## OlmoEarth Model Specs

| Model | Embed Dim | Encoder Params | HuggingFace ID |
|-------|-----------|----------------|----------------|
| Nano  | 192       | 1.4M           | `allenai/OlmoEarth-v1-Nano` |
| Tiny  | 384       | 6.2M           | `allenai/OlmoEarth-v1-Tiny` |
| Base  | 768       | 89M            | `allenai/OlmoEarth-v1-Base` |
| Large | 1024      | 308M           | `allenai/OlmoEarth-v1-Large` |

## Sentinel-2 L2A Bands

| Band | Resolution | Wavelength | Purpose |
|------|-----------|------------|---------|
| B02  | 10m       | 490nm (Blue) | Water, atmosphere |
| B03  | 10m       | 560nm (Green) | Vegetation vigor |
| B04  | 10m       | 665nm (Red) | Chlorophyll absorption |
| B05  | 20m       | 705nm (Red Edge 1) | Vegetation stress |
| B06  | 20m       | 740nm (Red Edge 2) | Canopy structure |
| B07  | 20m       | 783nm (Red Edge 3) | LAI estimation |
| B08  | 10m       | 842nm (NIR) | Biomass, moisture |
| B8A  | 20m       | 865nm (Narrow NIR) | Vegetation water |
| B11  | 20m       | 1610nm (SWIR 1) | Soil/vegetation moisture |
| B12  | 20m       | 2190nm (SWIR 2) | Geology, fire detection |
| B01  | 60m       | 443nm (Coastal) | Aerosol correction |
| B09  | 60m       | 945nm (Water Vapour) | Atmospheric water |

## Binary Embedding File Format

The output `.bin` file is readable by `olmoearth_bridge.zig` `EmbeddingLoader.loadFromFile()`:

```
Offset  Size    Field
0       4       tile_count (u32 little-endian)
4       2       embed_dim (u16 little-endian)
6       4*N*D   embeddings (f32 little-endian, row-major)
6+4*N*D 8*N     coordinates (f64 lat, f64 lon per tile, little-endian)
```

Where N = tile_count, D = embed_dim.

## Data Source

All Sentinel-2 data comes from Microsoft Planetary Computer (free, no account needed).
The `planetary-computer` Python package handles URL signing transparently.

STAC endpoint: `https://planetarycomputer.microsoft.com/api/stac/v1`
Collection: `sentinel-2-l2a`

## GF(3) Classification

| Trit | Zone Type | Satellite Signal | Example |
|------|-----------|-----------------|---------|
| +1   | high_density | Urban built-up, high NDVI variance | SF, NYC, Tokyo |
| 0    | emerging | Mixed land use, moderate change | Berlin, Bangalore |
| -1   | frontier | Agricultural/forest, low infrastructure | Lagos, Jakarta |

## References

- [OlmoEarth pretrain](https://github.com/allenai/olmoearth_pretrain)
- [OlmoEarth projects/tutorials](https://github.com/allenai/olmoearth_projects)
- [rslearn data tooling](https://github.com/allenai/rslearn)
- [Microsoft Planetary Computer](https://planetarycomputer.microsoft.com/)
- [Copernicus Sentinel-2 Mission](https://sentinels.copernicus.eu/web/sentinel/missions/sentinel-2)
- [zig-syrup WholeEarthModel](../../v/worlds/z/plurigrid/zig-syrup/src/whole_earth.zig)
