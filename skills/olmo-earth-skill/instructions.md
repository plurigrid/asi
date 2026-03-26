# olmo-earth-skill instructions

## Quick Start

```bash
# Download Sentinel-2 imagery and compute OlmoEarth embeddings
python /Users/alice/.claude/skills/olmo-earth-skill/sentinel2_olmoearth.py \
    --lat LAT --lon LON \
    --start YYYY-MM-DD --end YYYY-MM-DD \
    --output /tmp/embeddings.bin
```

## Arguments

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| `--lat` | yes | — | Center latitude |
| `--lon` | yes | — | Center longitude |
| `--start` | yes | — | Start date |
| `--end` | yes | — | End date |
| `--size` | no | 0.1 | Bounding box half-width (degrees) |
| `--max-cloud` | no | 15 | Max cloud cover % |
| `--model` | no | base | Model size: nano/tiny/base/large |
| `--crop` | no | 512 | Image crop in pixels |
| `--output` | no | /tmp/olmoearth_embeddings.bin | Output path |
| `--diff A B` | no | — | Compare two .bin files |

## Common Locations

| Place | Lat | Lon | Notes |
|-------|-----|-----|-------|
| SF Bay Area | 37.77 | -122.42 | PL high-density zone |
| NYC | 40.71 | -74.01 | PL high-density zone |
| London | 51.51 | -0.13 | PL high-density zone |
| Berlin | 52.52 | 13.41 | PL emerging zone |
| Lagos | 6.52 | 3.38 | PL frontier zone |
| Amazon basin | -3.47 | -62.22 | Deforestation monitoring |
| Sahel | 14.50 | 0.00 | Desertification tracking |

## Output Format

The `.bin` file is directly loadable by `olmoearth_bridge.zig` `EmbeddingLoader.loadFromFile()`:

```
[u32 tile_count][u16 embed_dim][f32 * N * D][f64 lat, f64 lon * N]
```

## Diff Mode

```bash
python sentinel2_olmoearth.py --diff /tmp/jan.bin /tmp/jul.bin
```

Reports per-tile cosine similarity statistics and identifies the tiles with the
most embedding drift (potential land-use change, deforestation, urbanization, etc.).

## Dependencies

Install with:
```bash
pip install olmoearth-pretrain torch planetary-computer pystac-client rasterio numpy
```

Or via uv for isolation:
```bash
uvx --from 'olmoearth-pretrain' --with torch --with planetary-computer \
    --with pystac-client --with rasterio --with numpy \
    python /Users/alice/.claude/skills/olmo-earth-skill/sentinel2_olmoearth.py --help
```

## Zig Integration

The output feeds directly into the zig-syrup WholeEarthModel:

```
sentinel2_olmoearth.py → .bin file → EmbeddingLoader.loadFromFile() → WholeEarthModel.setEmbedding()
```

Source: `/Users/alice/v/worlds/z/plurigrid/zig-syrup/src/olmoearth_bridge.zig`
