---
name: finder-color-walk
description: Deterministic triadic fanout over file-sets with macOS Finder label coloring, GF(3) conservation, and Strong Parallelism Invariance (SPI).
trit: 0
---

# finder-color-walk

Deterministic *triadic fanout* over a file-set, with macOS Finder label coloring, supporting **GF(3) conservation** and **Strong Parallelism Invariance (SPI)**.

## Contract

### Inputs
- Root path(s) to enumerate files (user-supplied).
- Optional filters (extensions, max depth, ignore globs).
- Policy:
  - `raw` (default): `color_at(file)` only; SPI holds; **GF(3) not guaranteed**.
  - `gf3_balanced`: colors are assigned in position-aligned triplets across the 3 routed fibers; **GF(3) holds**.

### Outputs
- A (file → color) assignment and a (file → fiber) routing.
- Optional application of macOS Finder label colors.

## Guarantees

### SPI (Strong Parallelism Invariance)
For a fixed file-set, policy, and seed:
- routing is deterministic and order-independent
- color assignment is deterministic and order-independent

Formally: any permutation of the same input file-set yields the same final mapping.

### GF(3) conservation (policy = `gf3_balanced`)
Let the three fibers be sorted lists `F0,F1,F2` of equal length `N`.
For each index `i` define trits `t0(i), t1(i), t2(i) ∈ {0,1,2}` as assigned to `F0[i],F1[i],F2[i]`.
Then for all `i`:
- `t0(i) + t1(i) + t2(i) ≡ 0 (mod 3)`

Implementation: choose `t0,t1` deterministically; set `t2 := (-t0-t1) mod 3`.

## Files
- `schema.jl` — Catlab ACSet schema: `FileColorWalk`.
- `triadic_router.bb` — GF(3)-balanced routing into 3 fibers.
- `finder_color_walk.bb` — single-stream walk (policy `raw`).
- `parallel_walk.bb` — 3-stream walk + `gf3_balanced` coloring.
- `spi_test.py` — verifies SPI + GF(3) (where requested).
- `INTERLEAVED.md` — 4-corpus synthesis notes.

## Quick start

### Route files into 3 fibers
```bash
bb triadic_router.bb --root . --out fibers.json
```

### Apply GF(3)-balanced colors (dry-run by default)
```bash
bb parallel_walk.bb --fibers fibers.json --policy gf3_balanced --dry-run
```

### Verify invariants
```bash
python spi_test.py --fibers fibers.json --policy gf3_balanced
```

## macOS Finder label mapping
Trits → label colors (customize inside scripts):
- 0: None
- 1: Green
- 2: Blue

## Related Skills (Backlinks)

| Skill | Trit | Integration |
|-------|------|-------------|
| [google-workspace](file:///Users/alice/.claude/skills/google-workspace/SKILL.md) | 0 | Drive file coloring via `drive_color_walk.py` |
| [gay-mcp](file:///Users/alice/.agents/skills/gay-mcp/SKILL.md) | +1 | SplitMix64 algorithm, trit-to-hue mapping |
| [triad-interleave](file:///Users/alice/.agents/skills/triad-interleave/SKILL.md) | +1 | Schedule file walks in balanced triplets |
| [bisimulation-game](file:///Users/alice/.agents/skills/bisimulation-game/SKILL.md) | -1 | Verify file state equivalence |
| [spi-parallel-verify](file:///Users/alice/.agents/skills/spi-parallel-verify/SKILL.md) | -1 | Strong Parallelism Invariance verification |

## Comparison with Related Skills

### vs gay-mcp
- **gay-mcp**: Pure color generation, OkLCH space, hex output
- **finder-color-walk**: File-focused, routing + coloring, Finder integration
- **Shared**: SplitMix64 RNG, GF(3) trits, SPI guarantee

### vs triad-interleave
- **triad-interleave**: Stream scheduling, temporal ordering
- **finder-color-walk**: Spatial routing into fibers
- **Shared**: 3-way balanced triplets, GF(3) conservation

### vs bisimulation-game
- **bisimulation-game**: State equivalence verification
- **finder-color-walk**: Deterministic state generation
- **Integration**: Use bisim to verify color assignments match across systems

## Integration Bridge

```python
# drive_color_walk.py bridges:
#   google-workspace MCP (file listing) 
#   → finder-color-walk (GF(3) routing)
#   → gay-mcp (color generation)
#   → Finder/Drive labels

from google_workspace import list_drive_items
from finder_color_walk import route_to_fibers, gf3_color
from gay import SplitMixTernary

files = list_drive_items(folder_id="root")
fibers = route_to_fibers(files, seed=0x42D)
colored = gf3_color(fibers, seed=0x42D)
# Apply to both Drive (via MCP) and Finder (via xattr)
```
