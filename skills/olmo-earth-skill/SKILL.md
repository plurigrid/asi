---
name: olmo-earth-skill
description: "Sentinel-2 satellite imagery to OlmoEarth embeddings on geodesic tiles, serialized via zig-syrup. Use for satellite imagery pipelines, earth observation embeddings, or WholeEarthModel operations."
---

# Whole Earth Model: Sentinel-2 + OlmoEarth + Zig-Syrup

Downloads Sentinel-2 satellite imagery from Microsoft Planetary Computer (free, no account needed), runs AI2's OlmoEarth foundation model to produce per-tile embeddings, and writes them into the zig-syrup WholeEarthModel binary format for CapTP exchange.

```
Planetary Computer (free Sentinel-2 COGs)
    |
    v
Download 12-band L2A tiles (10-60m resolution)
    |
    v
OlmoEarth FlexiVit Encoder (768-dim Base model)
    |
    v
Per-tile embeddings as f32 vectors
    |
    v
Binary file -> Zig EmbeddingLoader -> WholeEarthModel.setEmbedding()
    |
    v
Syrup serialization -> CapTP exchange at ~400 Hz
```

## Usage

### Download + Embed a region

```bash
python /Users/alice/.claude/skills/olmo-earth-skill/sentinel2_olmoearth.py \
    --lat 37.77 --lon -122.42 \
    --size 0.1 \
    --start 2024-07-01 --end 2024-08-31 \
    --max-cloud 10 \
    --model base \
    --output /tmp/sf_bay_embeddings.bin
```

### Load into zig-syrup WholeEarthModel

```zig
const bridge = @import("olmoearth_bridge");
const earth = @import("whole_earth");

var model = try earth.WholeEarthModel.init(allocator, .level_3, 768);
defer model.deinit();

var loader = bridge.EmbeddingLoader.init(allocator, .base);
var embeddings = try loader.loadFromFile("/tmp/sf_bay_embeddings.bin");
defer embeddings.deinit();

for (0..embeddings.tile_count) |i| {
    if (embeddings.getEmbedding(@intCast(i))) |emb| {
        const tile_id = model.tileAt(lat, lon) orelse continue;
        try model.setEmbedding(tile_id, emb);
    }
}

const syrup_val = try model.toSyrup(allocator);
```

### Compare tile embeddings over time

```bash
python sentinel2_olmoearth.py --lat 37.77 --lon -122.42 \
    --start 2024-01-01 --end 2024-03-31 --output /tmp/sf_q1.bin

python sentinel2_olmoearth.py --lat 37.77 --lon -122.42 \
    --start 2024-07-01 --end 2024-09-30 --output /tmp/sf_q3.bin

python sentinel2_olmoearth.py --diff /tmp/sf_q1.bin /tmp/sf_q3.bin
```

## OlmoEarth Model Specs

| Model | Embed Dim | Params | HuggingFace ID |
|-------|-----------|--------|----------------|
| Nano  | 192       | 1.4M   | `allenai/OlmoEarth-v1-Nano` |
| Tiny  | 384       | 6.2M   | `allenai/OlmoEarth-v1-Tiny` |
| Base  | 768       | 89M    | `allenai/OlmoEarth-v1-Base` |
| Large | 1024      | 308M   | `allenai/OlmoEarth-v1-Large` |

## Binary Embedding File Format

Readable by `olmoearth_bridge.zig` `EmbeddingLoader.loadFromFile()`:

```
Offset  Size    Field
0       4       tile_count (u32 little-endian)
4       2       embed_dim (u16 little-endian)
6       4*N*D   embeddings (f32 little-endian, row-major)
6+4*N*D 8*N     coordinates (f64 lat, f64 lon per tile, little-endian)
```

Where N = tile_count, D = embed_dim.

## Data Source

STAC endpoint: `https://planetarycomputer.microsoft.com/api/stac/v1`
Collection: `sentinel-2-l2a`
The `planetary-computer` Python package handles URL signing transparently.
