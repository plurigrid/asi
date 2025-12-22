---
name: acsets-algebraic-databases
description: "ACSets (Attributed C-Sets): Algebraic databases as in-memory data structures. Category-theoretic formalism for relational databases generalizing graphs and data frames."
source: AlgebraicJulia/ACSets.jl + music-topos
license: MIT
xenomodern: true
ironic_detachment: 0.73
---

# ACSets: Algebraic Databases Skill

> *"The category of simple graphs does not even have a terminal object!"*
> — AlgebraicJulia Blog, with characteristic ironic detachment

## What Are ACSets?

ACSets ("attributed C-sets") are a family of data structures generalizing both **graphs** and **data frames**. They are an efficient in-memory implementation of a category-theoretic formalism for relational databases.

**C-set** = Functor `X: C → Set` where C is a small category (schema)

```
┌─────────────────────────────────────────────────────────────┐
│  Schema (Small Category C)                                  │
│  ┌─────┐  src   ┌─────┐                                     │
│  │  E  │───────▶│  V  │                                     │
│  │     │  tgt   │     │                                     │
│  └──┬──┘───────▶└─────┘                                     │
│     │                                                       │
│     │ A C-set X assigns:                                    │
│     │   X(V) = set of vertices                              │
│     │   X(E) = set of edges                                 │
│     │   X(src): X(E) → X(V)                                 │
│     │   X(tgt): X(E) → X(V)                                 │
└─────────────────────────────────────────────────────────────┘
```

## Core Concepts

### 1. Schema Definition

```julia
using Catlab.CategoricalAlgebra

@present SchGraph(FreeSchema) begin
  V::Ob
  E::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
end

@acset_type Graph(SchGraph, index=[:src,:tgt])
```

### 2. Symmetric Graphs (Undirected)

```julia
@present SchSymmetricGraph <: SchGraph begin
  inv::Hom(E,E)

  compose(inv,src) == tgt
  compose(inv,tgt) == src
  compose(inv,inv) == id(E)
end

@acset_type SymmetricGraph(SchSymmetricGraph, index=[:src])
```

### 3. Attributed ACSets (with Data)

```julia
@present SchWeightedGraph <: SchGraph begin
  Weight::AttrType
  weight::Attr(E, Weight)
end

@acset_type WeightedGraph(SchWeightedGraph, index=[:src,:tgt]){Float64}
```

## GF(3) Conservation for ACSets

Integrate with Music Topos 3-coloring:

```julia
# Map ACSet parts to trits for GF(3) conservation
function acset_to_trits(g::Graph, seed::UInt64)
    rng = SplitMix64(seed)
    trits = Int[]
    for e in parts(g, :E)
        h = next_u64!(rng)
        hue = (h >> 16 & 0xffff) / 65535.0 * 360
        trit = hue < 60 || hue >= 300 ? 1 :
               hue < 180 ? 0 : -1
        push!(trits, trit)
    end
    trits
end

# Verify conservation: sum(trits) ≡ 0 (mod 3)
function gf3_conserved(trits)
    sum(trits) % 3 == 0
end
```

## Higher-Order Functions on ACSets

From Issue #7, implement functional patterns:

| Function | Description | Example |
|----------|-------------|---------|
| `map` | Transform parts | `map(g, :E) do e; ... end` |
| `filter` | Select parts by predicate | `filter(g, :V) { |v| degree(g,v) > 2 }` |
| `fold` | Aggregate over parts | `fold(+, g, :E, :weight)` |

## Open ACSets (Composable Interfaces)

```julia
# From Issue #89: Open versions of InterType ACSets
using ACSets.OpenACSetTypes

# Create open ACSet with exposed ports
@open_acset_type OpenGraph(SchGraph, [:V])

# Compose via pushout
g1 = OpenGraph(...)  # ports: v1, v2
g2 = OpenGraph(...)  # ports: v3, v4
g_composed = compose(g1, g2, [:v2 => :v3])
```

## Blog Post Series

1. **[Graphs and C-sets I](https://blog.algebraicjulia.org/post/2020/09/cset-graphs-1/)**: What is a graph?
2. **[Graphs and C-sets II](https://blog.algebraicjulia.org/post/2020/09/cset-graphs-2/)**: Half-edges and rotation systems
3. **[Graphs and C-sets III](https://blog.algebraicjulia.org/post/2021/04/cset-graphs-3/)**: Reflexive graphs and C-set homomorphisms
4. **[Graphs and C-sets IV](https://blog.algebraicjulia.org/post/2021/09/cset-graphs-4/)**: Propositional logic of subgraphs

## Citation

```bibtex
@article{patterson2022categorical,
  title={Categorical data structures for technical computing},
  author={Patterson, Evan and Lynch, Owen and Fairbanks, James},
  journal={Compositionality},
  volume={4},
  number={5},
  year={2022},
  doi={10.32408/compositionality-4-5}
}
```

## GeoACSets: Spatial + Categorical

[GeoACSets.jl](https://github.com/bmorphism/GeoACSets.jl) combines ACSets with geospatial capabilities:

> **Use morphisms for structural navigation, geometry for filtering.**

| Operation | Complexity | When to Use |
|-----------|------------|-------------|
| Morphism traversal | O(k) | Hierarchical containment |
| Spatial join | O(n log n) | Ad-hoc proximity queries |

### SpatialCity Schema

```julia
# 4-level hierarchy: Region → District → Parcel → Building
@present SchSpatialCity(FreeSchema) begin
    Region::Ob
    District::Ob
    Parcel::Ob
    Building::Ob
    
    district_of::Hom(District, Region)
    parcel_of::Hom(Parcel, District)
    building_on::Hom(Building, Parcel)
    
    GeomType::AttrType
    region_geom::Attr(Region, GeomType)
    footprint::Attr(Building, GeomType)
end

@acset_type SpatialCity(SchSpatialCity, 
    index=[:district_of, :parcel_of, :building_on])
```

### Traversal Patterns

```julia
# Downward: O(depth) via incident queries
buildings_in_region(city, region_id)

# Upward: O(1) via subpart lookups  
region_of_building(city, building_id)

# Combine spatial + morphism
nearby = spatial_filter(city, :Building, :footprint,
    g -> LibGEOS.distance(g, query_point) < 100)
for b in nearby
    district = traverse_up(city, b, :building_on, :parcel_of)
end
```

## OlmoEarth/Terra Extension (Spatio-Temporal)

GeoACSets needs extension for foundation model integration:

### SchOlmoEarthPatch

```julia
@present SchOlmoEarthPatch(FreeSchema) begin
    Patch::Ob           # Variable-size spatial patch
    Timestep::Ob        # Monthly temporal unit
    Modality::Ob        # Sentinel-1/2, Landsat, Maps
    Token::Ob           # Encoded representation
    View::Ob            # For instance contrastive
    
    patch_timestep::Hom(Patch, Timestep)
    patch_modality::Hom(Patch, Modality)
    token_patch::Hom(Token, Patch)
    
    # Masking as structured decomposition
    MaskedPatch::Ob
    MaskConfig::Ob
    masked_patch::Hom(MaskedPatch, Patch)
    mask_state::Attr(MaskedPatch, MaskStateType)  # encode/decode/both/none
end
```

### Masking as Span Decomposition

```julia
# OlmoEarth masking creates:
#   EncodeBag ← Apex (both) → DecodeBag

function create_masking_decomposition(patches, config_id)
    encode_bag = filter(p -> mask_state(p) ∈ [:encode_only, :both], patches)
    decode_bag = filter(p -> mask_state(p) ∈ [:decode_only, :both], patches)
    apex = filter(p -> mask_state(p) == :both, patches)
    (encode_bag, apex, decode_bag)
end
```

### Instance Contrastive as Sheaf Condition

```julia
# Two views must agree on pooled representation
function verify_sheaf_condition(patches; threshold=0.99)
    pooled1 = patches[view1, :pooled_repr]
    pooled2 = patches[view2, :pooled_repr]
    cosine_sim(pooled1, pooled2) >= threshold
end
```

## Related Packages

- **[Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl)**: Full categorical algebra (homomorphisms, limits, colimits)
- **[AlgebraicRewriting.jl](https://github.com/AlgebraicJulia/AlgebraicRewriting.jl)**: Declarative rewriting for ACSets
- **[AlgebraicDynamics.jl](https://github.com/AlgebraicJulia/AlgebraicDynamics.jl)**: Compositional dynamical systems
- **[GeoACSets.jl](https://github.com/bmorphism/GeoACSets.jl)**: Spatial geometry + morphism navigation
- **[StructuredDecompositions.jl](https://github.com/AlgebraicJulia/StructuredDecompositions.jl)**: Sheaf-based decision problems

## Xenomodern Integration

The ironic detachment comes from recognizing that:

1. **Category theory isn't about abstraction for its own sake** — it's about finding the *right* abstractions that compose
2. **Simple graphs are actually badly behaved** — the terminal object problem reveals hidden assumptions
3. **Functors are data structures** — this reframes databases as applied category theory

```
         xenomodernity
              │
    ┌─────────┴─────────┐
    │                   │
 ironic              sincere
detachment          engagement
    │                   │
    └─────────┬─────────┘
              │
      C-sets as functors
      (both ironic AND sincere)
```

## Commands

```bash
just acset-demo          # Run ACSet demonstration
just acset-graph         # Create and visualize graph
just acset-symmetric     # Symmetric graph example
just acset-gf3           # Check GF(3) conservation
```
