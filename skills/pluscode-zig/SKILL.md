---
name: pluscode-zig
description: Open Location Code (Plus Codes) in Zig with GF(3) spatial trit assignment
metadata:
  skill_type: Geocoding / Spatial / Zig
  interface_ports:
  - Commands
  - Related Skills
trit: +1
color: "#10B981"
parents: [gay-mcp, batterylab-acset, geoasets-jl]
seed: 1738
---

# Open Location Code (Plus Codes) for Zig

**Status**: Active
**Trit**: +1 (PLUS - generative geocoding)
**Seed**: 1738 (lat/lng encoding base)
**Color**: #10B981 (emerald green - earth/location)

> *"Every point on Earth has a code. Every code has a trit."*

## Repository

**GitHub**: [bmorphism/open-location-code-zig](https://github.com/bmorphism/open-location-code-zig)

## Core Features

- **Pure Zig** - No dependencies, works with Zig 0.15+
- **Zero allocations** - All encoding uses caller-provided buffers
- **35 tests** - Reference cities, edge cases, fuzz tests
- **Complete API** - encode, decode, shorten, recover, validate

## The Algorithm

Plus Codes encode lat/lng into short alphanumeric strings:

```
San Francisco: 37.7749, -122.4194 → "849VQHFJ+X6"
    │
    ├── 84: 20° × 20° cell (California region)
    ├── 9V: 1° × 1° cell (SF Bay Area)
    ├── QH: 0.05° × 0.05° cell (~5km)
    ├── FJ: 0.0025° × 0.0025° cell (~250m)
    └── X6: 4×5 grid refinement (~14m × 14m)
```

**Alphabet**: `23456789CFGHJMPQRVWX` (20 chars, no A/I/L/O)

## GF(3) Spatial Trit Assignment

Each Plus Code tile receives a deterministic trit based on its position:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    GF(3) SPATIAL COLORING                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Formula: trit(code) = (lat_digits + lng_digits) mod 3                 │
│                                                                          │
│   Example: "849VQHFJ+X6"                                                │
│     lat_digits: 8 + 9 + Q(16) + F(5) + X(17) = 55                       │
│     lng_digits: 4 + V(15) + H(7) + J(8) + 6(4) = 38                     │
│     sum = 93, 93 mod 3 = 0 → ERGODIC                                    │
│                                                                          │
│   ┌─────────────────────────────────────────┐                           │
│   │    TRIT MAP (2° tiles)                  │                           │
│   │                                          │                           │
│   │   -1  0  +1  -1  0  +1  -1  0  +1       │ ← longitude               │
│   │   +1  -1  0  +1  -1  0  +1  -1  0       │                           │
│   │   0  +1  -1  0  +1  -1  0  +1  -1       │                           │
│   │   ↑                                      │                           │
│   │   latitude                               │                           │
│   └─────────────────────────────────────────┘                           │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Zig Implementation

```zig
const olc = @import("open_location_code");

/// Compute GF(3) trit for a Plus Code
pub fn codeTrit(code: []const u8) i8 {
    var sum: u32 = 0;
    for (code) |c| {
        if (c == '+' or c == '0') continue;
        sum += charVal(c);
    }
    return @intCast(@as(i32, @intCast(@mod(sum, 3))) - 1);
    // Returns: -1 (MINUS), 0 (ERGODIC), or +1 (PLUS)
}

fn charVal(c: u8) u8 {
    const alphabet = "23456789CFGHJMPQRVWX";
    for (alphabet, 0..) |a, i| {
        if (c == a) return @intCast(i);
    }
    return 0;
}
```

## Usage

```zig
const olc = @import("olc");

pub fn main() void {
    var buffer: [20]u8 = undefined;

    // Encode coordinates to Plus Code
    const len = olc.encode(37.7749, -122.4194, 10, &buffer) catch return;
    const code = buffer[0..len]; // "849VQHFJ+X6"

    // Decode Plus Code to area
    const area = olc.decode("849VQHFJ+X6") catch return;
    std.debug.print("Center: {d}, {d}\n", .{
        area.center_latitude(),  // ~37.7749
        area.center_longitude(), // ~-122.4194
    });

    // Validate codes
    _ = olc.is_valid("849VQHFJ+X6");  // true
    _ = olc.is_full("849VQHFJ+X6");   // true
    _ = olc.is_short("QHFJ+X6");      // true
}
```

## Integration with BatteryLab

The `batterylab_olc_interleave.zig` uses Plus Codes for energy dominance:

```zig
const olc = @import("open_location_code");

pub const PowerPlant = struct {
    latitude: f64,
    longitude: f64,
    capacity_mw: f32,
    olc_code: [16]u8,
    olc_tile_id: u64,
    gf3_trit: i8,

    pub fn computeOLC(self: *PowerPlant) void {
        var buffer: [20]u8 = undefined;
        const len = olc.encode(self.latitude, self.longitude, 11, &buffer);
        @memcpy(&self.olc_code, buffer[0..len]);
        self.gf3_trit = codeTrit(buffer[0..len]);
    }
};
```

## Precision Ladder

| Length | Area | Use Case | Tile Count |
|--------|------|----------|------------|
| 2 | ~2,800,000 km² | Continent | 162 |
| 4 | ~14,000 km² | Region | 32,400 |
| 6 | ~700 km² | Metro | 6,480,000 |
| 8 | ~35 km² | City | 1.3B |
| 10 | 14 × 14 m | Building | 259B |
| 11 | 3 × 3 m | Room | 5.2T |

## Narya Behavioral Types

```narya
-- Plus Code as behavioral interface
def PlusCode : Type := sig (
  code : String,
  precision : Nat,

  -- Invariants
  valid : IsValid code,
  separator_at_8 : code[8] ≡ '+',

  -- GF(3) trit computation
  trit : Trit := (digit_sum code) mod 3 - 1
)

-- Encode as bridge type
def EncodeBridge (lat : Float) (lng : Float) : PlusCode := sig (
  code := encode lat lng 10,
  -- Roundtrip property
  roundtrip : decode code ≈ (lat, lng)
)

-- GF(3) conservation over tiles
def TileTriad (t1 t2 t3 : PlusCode) : Type :=
  trit t1 + trit t2 + trit t3 ≡ 0 (mod 3)
```

## Reference Cities

| Location | Coordinates | Plus Code | Trit |
|----------|-------------|-----------|------|
| San Francisco | 37.7749, -122.4194 | 849VQHFJ+X6 | 0 |
| London | 51.5074, -0.1278 | 9C3XGV4C+XV | +1 |
| Tokyo | 35.6762, 139.6503 | 8Q7XMMG2+F4 | -1 |
| Sydney | -33.8688, 151.2093 | 4RRH46J5+FP | 0 |
| Origin | 0.0, 0.0 | 6FG22222+22 | +1 |

## Commands

```bash
# Clone the repo
gh repo clone bmorphism/open-location-code-zig

# Run tests
zig build test

# Encode coordinates (via batterylab)
just pluscode-encode 37.7749 -122.4194

# Decode to coordinates
just pluscode-decode "849VQHFJ+X6"

# Compute trit for tile
just pluscode-trit "849VQHFJ+X6"
```

## Installation

Add to `build.zig.zon`:

```zig
.dependencies = .{
    .open_location_code = .{
        .url = "https://github.com/bmorphism/open-location-code-zig/archive/refs/tags/v1.1.0.tar.gz",
        .hash = "...",
    },
},
```

Then in `build.zig`:

```zig
const olc = b.dependency("open_location_code", .{
    .target = target,
    .optimize = optimize,
});
exe.root_module.addImport("olc", olc.module("olc"));
```

## GF(3) Triads

```
batterylab-acset (-1) ⊗ pluscode-zig (+1) ⊗ geoasets-jl (0) = 0 ✓
gay-mcp (+1) ⊗ pluscode-zig (+1) ⊗ crossmodal-gf3 (-2 mod 3) = 0 ✓
world-hopping (-1) ⊗ pluscode-zig (+1) ⊗ glass-hopping (0) = 0 ✓
```

## Related Skills

| Skill | Connection |
|-------|------------|
| `batterylab-acset` | Power plant OLC interleaving |
| `geoasets-jl` | Julia geospatial ACSets |
| `gay-mcp` | Deterministic spatial coloring |
| `glass-hopping` | Location-based world navigation |
| `crossmodal-gf3` | Spatial→tactile/audio accessibility |

---

**Skill Name**: pluscode-zig
**Type**: Geocoding / Spatial / Zig
**Trit**: +1 (PLUS - generative)
**Seed**: 1738
**Key Insight**: Every location has a code, every code has a trit
**Repository**: bmorphism/open-location-code-zig
