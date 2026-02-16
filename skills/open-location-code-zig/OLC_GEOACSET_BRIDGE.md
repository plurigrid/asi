# OLC ↔ GeoACSets Bidirectional Bridge

**Rewrite-time accuracy verification for Plus Codes**

## The Problem

When using Plus Codes for:
- Teleportation tests (instant position change)
- Fokker-Planck scale verification (diffusion across tiles)
- Volume tests (capacity aggregation)

We need **bidirectional index verification** at rewrite time to ensure:
1. Encode(lat, lng) → code → Decode → (lat', lng') roundtrips within tolerance
2. Parent/child tile containment is exact
3. GF(3) trits conserve across tile hierarchies

## Schema: SchOLCTileHierarchy

```julia
using ACSets, GeoACSets

"""
OLC Tile Hierarchy - 6 precision levels with bidirectional morphisms

Hierarchy:
  P2 (20°×20°) ← P4 (1°×1°) ← P6 (0.05°×0.05°) ← P8 ← P10 ← P11

Morphisms encode CONTAINMENT (child tile is inside parent).
Indexed for O(1) up-traversal, O(k) down-traversal.
"""
const SchOLCTileHierarchy = BasicSchema(
    [:P2, :P4, :P6, :P8, :P10, :P11],  # Objects (precision levels)
    [
        (:p2_of, :P4, :P2),    # P4 tile → containing P2 tile
        (:p4_of, :P6, :P4),    # P6 tile → containing P4 tile
        (:p6_of, :P8, :P6),    # etc.
        (:p8_of, :P10, :P8),
        (:p10_of, :P11, :P10),
    ],
    [:Code, :Lat, :Lng, :Trit],  # Attribute types
    [
        # OLC code strings
        (:code_p2, :P2, :Code),
        (:code_p4, :P4, :Code),
        (:code_p6, :P6, :Code),
        (:code_p8, :P8, :Code),
        (:code_p10, :P10, :Code),
        (:code_p11, :P11, :Code),
        # Centroid coordinates
        (:lat_p2, :P2, :Lat), (:lng_p2, :P2, :Lng),
        (:lat_p4, :P4, :Lat), (:lng_p4, :P4, :Lng),
        (:lat_p6, :P6, :Lat), (:lng_p6, :P6, :Lng),
        (:lat_p8, :P8, :Lat), (:lng_p8, :P8, :Lng),
        (:lat_p10, :P10, :Lat), (:lng_p10, :P10, :Lng),
        (:lat_p11, :P11, :Lat), (:lng_p11, :P11, :Lng),
        # GF(3) trits
        (:trit_p2, :P2, :Trit),
        (:trit_p4, :P4, :Trit),
        (:trit_p6, :P6, :Trit),
        (:trit_p8, :P8, :Trit),
        (:trit_p10, :P10, :Trit),
        (:trit_p11, :P11, :Trit),
    ]
)

@acset_type OLCTileHierarchy(SchOLCTileHierarchy,
    index=[:p2_of, :p4_of, :p6_of, :p8_of, :p10_of])
```

## Bidirectional Traversal

```julia
"""
Up-traversal: P11 tile → P2 region (O(5) - constant)
"""
function region_of_tile(tiles::OLCTileHierarchy, p11_id::Int)
    p10 = tiles[p11_id, :p10_of]
    p8 = tiles[p10, :p8_of]
    p6 = tiles[p8, :p6_of]
    p4 = tiles[p6, :p4_of]
    p2 = tiles[p4, :p2_of]
    return p2
end

"""
Down-traversal: P2 region → all P11 tiles (O(20^5) worst case)
"""
function tiles_in_region(tiles::OLCTileHierarchy, p2_id::Int)
    p4s = incident(tiles, p2_id, :p2_of)
    p6s = reduce(vcat, [incident(tiles, p, :p4_of) for p in p4s]; init=Int[])
    p8s = reduce(vcat, [incident(tiles, p, :p6_of) for p in p6s]; init=Int[])
    p10s = reduce(vcat, [incident(tiles, p, :p8_of) for p in p8s]; init=Int[])
    p11s = reduce(vcat, [incident(tiles, p, :p10_of) for p in p10s]; init=Int[])
    return p11s
end
```

## Rewrite-Time Verification

### 1. Encode Roundtrip

```julia
"""
Verify Zig encode matches Julia decode (and vice versa).
Called at rewrite time to detect drift.
"""
function verify_roundtrip(lat::Float64, lng::Float64;
                          zig_encode::Function, julia_decode::Function)
    # Zig encodes
    code = zig_encode(lat, lng, 10)

    # Julia decodes
    area = julia_decode(code)
    lat_decoded = (area.south + area.north) / 2
    lng_decoded = (area.west + area.east) / 2

    # Tolerance: 1/2 tile width at precision 10 (~7m)
    lat_tolerance = 0.000125 / 2
    lng_tolerance = 0.000125 / 2

    lat_ok = abs(lat - lat_decoded) < lat_tolerance
    lng_ok = abs(lng - lng_decoded) < lng_tolerance

    return lat_ok && lng_ok, (lat_decoded, lng_decoded)
end
```

### 2. Containment Verification

```julia
"""
Verify parent tile actually contains child tile geometrically.
Detects edge-case bugs in Zig implementation.
"""
function verify_containment(tiles::OLCTileHierarchy, p11_id::Int)
    # Get child centroid
    child_lat = tiles[p11_id, :lat_p11]
    child_lng = tiles[p11_id, :lng_p11]

    # Traverse up and check each parent contains child
    p10 = tiles[p11_id, :p10_of]
    p10_area = decode_bounds(tiles[p10, :code_p10])
    @assert child_lat >= p10_area.south && child_lat <= p10_area.north
    @assert child_lng >= p10_area.west && child_lng <= p10_area.east

    # Continue for all levels...
    return true
end
```

### 3. GF(3) Conservation

```julia
"""
Verify triadic conservation at rewrite time.
Sum of trits across any triadic selection must ≡ 0 (mod 3).
"""
function verify_gf3_conservation(tiles::OLCTileHierarchy,
                                  tile_ids::Vector{Int},
                                  precision::Symbol)
    trit_attr = Symbol("trit_", precision)
    total = sum(tiles[t, trit_attr] for t in tile_ids)
    return mod(total, 3) == 0
end
```

## Fokker-Planck Scale Verification

The Fokker-Planck equation describes diffusion:

```
∂ρ/∂t = D ∇²ρ - ∇·(vρ)
```

For OLC tiles, this becomes a discrete random walk where:
- Each P11 tile has neighbors (4 cardinal + 4 diagonal)
- Transition probability depends on tile boundary length
- GF(3) conservation must hold at each timestep

```julia
"""
Fokker-Planck step: probability flows between adjacent tiles.
Verifies GF(3) conservation survives diffusion.
"""
function fokker_planck_step!(density::Dict{Int, Float64},
                              tiles::OLCTileHierarchy,
                              diffusion_coeff::Float64)
    new_density = Dict{Int, Float64}()

    for (tile_id, ρ) in density
        # Get neighbors (tiles sharing boundary)
        neighbors = get_neighbors(tiles, tile_id)

        # Diffuse to neighbors
        outflow = diffusion_coeff * ρ * length(neighbors)
        new_density[tile_id] = get(new_density, tile_id, 0.0) + (ρ - outflow)

        for n in neighbors
            new_density[n] = get(new_density, n, 0.0) + outflow / length(neighbors)
        end
    end

    # Verify GF(3) conservation: weighted trit sum unchanged
    before_trit_sum = sum(ρ * tiles[t, :trit_p11] for (t, ρ) in density)
    after_trit_sum = sum(ρ * tiles[t, :trit_p11] for (t, ρ) in new_density)
    @assert abs(before_trit_sum - after_trit_sum) < 1e-10 "GF(3) not conserved!"

    merge!(density, new_density)
end
```

## Teleportation Test

```julia
"""
Teleportation: instant position change.
Verifies bidirectional index coherence after discontinuous jump.
"""
function teleportation_test(tiles::OLCTileHierarchy,
                            from_lat::Float64, from_lng::Float64,
                            to_lat::Float64, to_lng::Float64)
    # Encode both positions
    from_code = encode(from_lat, from_lng, 11)
    to_code = encode(to_lat, to_lng, 11)

    # Look up in ACSet
    from_id = findfirst(p -> tiles[p, :code_p11] == from_code, parts(tiles, :P11))
    to_id = findfirst(p -> tiles[p, :code_p11] == to_code, parts(tiles, :P11))

    # Verify up-traversal is coherent for both
    from_region = region_of_tile(tiles, from_id)
    to_region = region_of_tile(tiles, to_id)

    # Verify down-traversal recovers original tiles
    from_tiles = tiles_in_region(tiles, from_region)
    to_tiles = tiles_in_region(tiles, to_region)

    @assert from_id ∈ from_tiles "Bidirectional coherence failed for from_tile"
    @assert to_id ∈ to_tiles "Bidirectional coherence failed for to_tile"

    return true
end
```

## Zig ↔ Julia Interchange Format

```json
{
  "format": "olc-geoacset-v1",
  "tiles": [
    {
      "code": "849VQHFJ+X6",
      "precision": 10,
      "centroid": [37.7749, -122.4194],
      "bounds": {
        "south": 37.77475,
        "north": 37.77500,
        "west": -122.41950,
        "east": -122.41925
      },
      "trit": 0,
      "parent_code": "849VQHFJ+"
    }
  ],
  "verification": {
    "roundtrip_tolerance": 0.0000625,
    "gf3_conserved": true,
    "fokker_planck_steps": 1000,
    "teleportation_tests": 100
  }
}
```

## Related Skills

| Skill | Role |
|-------|------|
| `pluscode-zig` | Zig encode/decode implementation |
| `geoasets-jl` | Julia ACSet spatial hierarchy |
| `fokker-planck-analyzer` | Diffusion verification |
| `glass-hopping` | Location-based world navigation |
| `tritwies-trace` | GF(3) conservation tracking |

---

**Bridge Type**: OLC ↔ GeoACSets
**Purpose**: Rewrite-time accuracy verification
**Verification**: Roundtrip, containment, GF(3) conservation
**Tests**: Fokker-Planck diffusion, teleportation coherence
