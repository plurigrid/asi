---
name: rio-webgpu-tiles
description: WebGPU tile rendering for Rio Terminal via wgpu and sugarloaf. Extends
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Rio WebGPU Tiles

GPU-accelerated tile rendering in Rio Terminal using wgpu and the sugarloaf brush architecture.

## Architecture Overview

```
OSC 1337 Sequence → rio-backend (parse) → RioEvent::InsertTile → rioterm (frontend) → sugarloaf TileBrush → wgpu render
```

### Core Files
| File | Purpose |
|------|---------|
| `sugarloaf/src/components/tiles/mod.rs` | TileBrush, TileWorldState, GPU buffers |
| `sugarloaf/src/sugarloaf.rs` | Main renderer integration, public API |
| `rio-backend/src/ansi/tile_protocol.rs` | OSC 1337 `Tile=` parsing |
| `rio-backend/src/performer/handler.rs` | OSC dispatch to handler |
| `rio-backend/src/event/mod.rs` | `InsertTile` event variant |
| `frontends/rioterm/src/application.rs` | Frontend event handling |

## Protocol: OSC 1337 Tile Extension

```bash
# Format: ESC ] 1337 ; Tile = key:value,key:value,... BEL
printf '\033]1337;Tile=shader:plasma,x:50,y:50,w:200,h:150\007'
```

### Parameters
| Key | Type | Description |
|-----|------|-------------|
| `shader` | string | `plasma`, `clock`, `noise`, or custom ID |
| `x`, `y` | f32 | Position in pixels |
| `w`, `h` | f32 | Size in pixels |
| `id` | u64 | Tile ID (0 = auto-assign) |
| `kind` | string | `persistent` (default) or `transient` |
| `r`, `g`, `b`, `a` | f32 | Custom color/data (0.0-1.0) |
| `time_offset` | f32 | Animation time offset |

## Tile Lifecycle

### Persistent Tiles
Remain until explicitly removed by ID:
```rust
let id = sugarloaf.create_persistent_tile(scene);
// ... later
sugarloaf.remove_persistent_tile(id);
```

### Transient Tiles
Cleared at `begin_frame()`, must be re-pushed each frame:
```rust
sugarloaf.push_transient_tile(scene);
```

## TileWorldState

Manages CPU state with high-precision time (f64), converted to modular f32 for GPU:

```rust
pub struct TileWorldState {
    persistent: HashMap<TileId, TileScene>,
    transient: Vec<TileScene>,
    world_time_seconds: f64,
    next_id: TileId,
}

impl TileWorldState {
    pub fn begin_frame(&mut self,