---
name: acsets-algebraic-databases
description: "ACSets (Attributed C-Sets): Algebraic databases as in-memory data structures. Category-theoretic formalism for relational databases generalizing graphs and data frames."
source: AlgebraicJulia/ACSets.jl + music-topos
license: MIT
xenomodern: true
ironic_detachment: 0.73
<<<<<<< HEAD
=======
trit: 0
triangulated: 2025-12-22
>>>>>>> origin/feature/skill-connectivity-hub-20251226
---

# ACSets: Algebraic Databases Skill

> *"The category of simple graphs does not even have a terminal object!"*
<<<<<<< HEAD
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
=======
> — AlgebraicJulia Blog

## What Are ACSets?

**C-set** = Functor `X: C → Set` where C is a small category (schema)

```
Schema C           C-set X: C → Set
┌─────┐  src      X(V) = {v1,v2,v3}
│  E  │──────▶    X(E) = {e1,e2}
│     │  tgt      X(src)(e1) = v1
└─────┘──────▶    X(tgt)(e1) = v2
```

---

## Core Schemas

```julia
@present SchGraph(FreeSchema) begin
  V::Ob; E::Ob
  src::Hom(E,V); tgt::Hom(E,V)
end
@acset_type Graph(SchGraph, index=[:src,:tgt])

# Symmetric (undirected)
@present SchSymmetricGraph <: SchGraph begin
  inv::Hom(E,E)
  compose(inv,src) == tgt
  compose(inv,inv) == id(E)
end

# Attributed
>>>>>>> origin/feature/skill-connectivity-hub-20251226
@present SchWeightedGraph <: SchGraph begin
  Weight::AttrType
  weight::Attr(E, Weight)
end
<<<<<<< HEAD

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

## Related Packages

- **[Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl)**: Full categorical algebra (homomorphisms, limits, colimits)
- **[AlgebraicRewriting.jl](https://github.com/AlgebraicJulia/AlgebraicRewriting.jl)**: Declarative rewriting for ACSets
- **[AlgebraicDynamics.jl](https://github.com/AlgebraicJulia/AlgebraicDynamics.jl)**: Compositional dynamical systems

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
=======
@acset_type WeightedGraph(SchWeightedGraph){Float64}
```

---

## ∫G: Category of Elements

Converts ACSet into category (shape for decompositions):

```julia
G = @acset Graph begin V=3; E=2; src=[1,2]; tgt=[2,3] end
∫G = ∫(G)  # Objects: (V,1),(V,2),(V,3),(E,1),(E,2)
```

---

## Wiring Diagrams (AlgebraicDynamics)

```julia
@present SchUWD(FreeSchema) begin
  Box::Ob; Port::Ob; Junction::Ob; OuterPort::Ob
  box::Hom(Port, Box)
  junction::Hom(Port, Junction)
  outer_junction::Hom(OuterPort, Junction)
end

# oapply = colimit of component diagram
composite = oapply(wiring_diagram, components)
```

---

## Time-Varying ACSets

```julia
@present SchTimeVarying(FreeSchema) begin
  Interval::Ob; Snapshot::Ob; State::Ob
  timestamp::Hom(Snapshot, Interval)
  observable::Hom(Snapshot, State)
  Time::AttrType; Value::AttrType
end
# Colimit reconstructs dynamics (DMD = colimit of snapshot diagram)
```

---

## 𝐃 Functor: Lifting Problems

```julia
# k-coloring as functor
k_coloring(G) = homomorphisms(G, complete_graph(k))

# Lift to solution decomposition
solution = 𝐃(k_coloring, decomp, CoDecomposition)
(answer, witness) = decide_sheaf_tree_shape(k_coloring, decomp)
```

---

## Open ACSets

```julia
@open_acset_type OpenGraph(SchGraph, [:V])
g_composed = compose(g1, g2, [:v2 => :v3])  # Pushout
```

---

## GF(3) Triads

```
bumpus-width (-1) ⊗ acsets (0) ⊗ libkind-directed (+1) = 0 ✓  [FPT]
schema-valid (-1) ⊗ acsets (0) ⊗ oapply-colimit (+1) = 0 ✓  [Composition]
temporal-coal (-1) ⊗ acsets (0) ⊗ koopman-gen (+1) = 0 ✓  [Dynamics]
```

---

## Specter Navigation (NEW 2025-12-22)

Zero-overhead ACSet navigation via Specter-style paths:

### Benchmark Results

| Operation | Hand-Written | Optimized Specter | Ratio |
|-----------|--------------|-------------------|-------|
| Select field | - | 386.4 ns | ~2x |
| Navigate 4 levels | 735.7 ns | 394.9 ns | **1.9x faster** |

### ACSet Navigators

```julia
# Navigate schema objects and morphisms
acset_field(:E, :src)      # Select all source vertices
acset_field(:E, :tgt)      # Select all target vertices
acset_where(:E, :src, ==(1))  # Filter edges by predicate
acset_parts(:V)            # Navigate to all parts of object

# Compose paths
path = (acset_parts(:E), acset_field(:E, :src))
select(path, graph)  # All source vertices of all edges
```

### Correct-by-Construction

ACSet navigation follows 3-MATCH principles:
- **Local**: Field names checked at compile time
- **Global**: Path correctness guaranteed
- **GF(3)**: sheaf-cohomology (-1) ⊗ acsets (0) ⊗ gay-mcp (+1) = 0

---

## Edge Growth Rules (NEW 2025-12-22)

ACSet-based edge growth with spectral constraints:

### Ramanujan-Preserving Growth

```julia
@present SchRamanujanGraph <: SchGraph begin
  SpectralData::AttrType
  lambda2::Attr(V, SpectralData)  # Track λ₂ per growth step
end

function grow_edge_ramanujan!(G::ACSet, u, v)
    """
    Add edge preserving Ramanujan property.
    Uses Alon-Boppana bound: λ₂ ≥ 2√(d-1).
    """
    d = degree(G)
    bound = 2 * sqrt(d - 1)
    
    # Tentatively add edge
    add_part!(G, :E, src=u, tgt=v)
    
    # Check spectral constraint
    λ₂ = second_eigenvalue(adjacency_matrix(G))
    
    if λ₂ > bound + 0.01  # Tolerance
        # Rollback: remove edge
        rem_part!(G, :E, nparts(G, :E))
        return false
    end
    
    return true
end
```

### Non-Backtracking Edge Schema

```julia
@present SchNonBacktracking(FreeSchema) begin
  V::Ob; E::Ob; DE::Ob  # DE = directed edges
  src::Hom(E,V); tgt::Hom(E,V)
  forward::Hom(E, DE); backward::Hom(E, DE)
  de_src::Hom(DE, V); de_tgt::Hom(DE, V)
  
  # Non-backtracking constraint: head(e) = tail(f) ∧ e ≠ f⁻¹
  nonbacktrack::Hom(DE, DE)  # B matrix as morphism
end

# Ihara zeta via ACSet homomorphisms
function prime_cycles(G::ACSet, max_length)
    cycles = []
    for k in 1:max_length
        if moebius(k) != 0  # Only squarefree lengths
            push!(cycles, find_cycles(G, k))
        end
    end
    return cycles
end
```

### Centrality via Möbius Inversion

```julia
function alternating_centrality(G::ACSet)
    """
    Centrality via Möbius-weighted path counts.
    c(v) = Σ_{k} μ(k) × paths_k(v) / k
    """
    n = nparts(G, :V)
    A = adjacency_matrix(G)
    c = zeros(n)
    
    for k in 1:diameter(G)
        μ_k = moebius(k)
        if μ_k != 0
            paths_k = diag(A^k)
            c .+= μ_k .* paths_k ./ k
        end
    end
    
    return c ./ sum(abs.(c))
end
```

---

## Spectral Bundle Triads

```
ramanujan-expander (-1) ⊗ acsets (0) ⊗ gay-mcp (+1) = 0 ✓  [Graph Coloring]
ramanujan-expander (-1) ⊗ acsets (0) ⊗ moebius-inversion (+1) = 0 ✓  [Edge Growth]
ihara-zeta (-1) ⊗ acsets (0) ⊗ moebius-inversion (+1) = 0 ✓  [Prime Cycles]
```

---

## StructACSet Internals (DeepWiki 2025-12-22)

Schema and attribute types known at compile time, enabling performance optimizations.

### Type Parameters

```julia
StructACSet{S, Ts, PT}
# S  = TypeLevelSchema{Symbol} - schema at compile time
# Ts = Tuple of Julia types for attributes (e.g., Float64 for Weight)
# PT = PartsType strategy (IntParts or BitSetParts)
```

### Column Storage

```julia
struct StructACSet{S, Ts, PT}
  parts::NamedTuple     # {:V => IntParts, :E => IntParts, ...}
  subparts::NamedTuple  # {:src => Column, :tgt => Column, :weight => Column, ...}
end

# Column types:
# - Homs: Vector{Int} mapping parts to parts
# - Attrs: Vector{Union{AttrVar,T}} for attribute values
```

### Index Configuration

```julia
@acset_type Graph(SchGraph, 
    index=[:src, :tgt],         # Preimage cache: O(1) incident queries
    unique_index=[:inv]          # Injective cache: even faster
)

# Index types:
# - NoIndex: Linear scan O(n)
# - Index (StoredPreimageCache): O(1) average via hash
# - UniqueIndex (InjectiveCache): O(1) guaranteed, injective morphisms only
```

### Part ID Allocation Strategies

| Strategy | Type | Deletion | Use Case |
|----------|------|----------|----------|
| **IntParts** | DenseParts | Pop-and-swap (renumbers) | Fast, compact storage |
| **BitSetParts** | MarkAsDeleted | Preserves IDs, requires gc!() | Stable references |

```julia
# IntParts (default): contiguous IDs 1..n
add_parts!(G, :V, 3)  # IDs: 1, 2, 3
rem_part!(G, :V, 2)   # ID 3 → 2, ID 2 gone

# BitSetParts: sparse IDs with gaps
rem_part!(G, :V, 2)   # ID 2 marked deleted, ID 3 unchanged
gc!(G)                # Compact: removes gaps
```

### Performance Optimizations

1. **Compile-time dispatch**: `Val{S}`, `Val{Ts}` for static method selection
2. **Columnar storage**: Cache-friendly, vectorizable access patterns
3. **Preimage caching**: `incident(G, v, :src)` is O(1) with index
4. **`@ct_enable`**: Compile-time schema validation in `_set_subpart!`

### ACSet Variants

| Variant | Schema | Types | Performance |
|---------|--------|-------|-------------|
| **StructACSet** | Type parameter | Type parameter | Optimal (compile-time) |
| **DynamicACSet** | Field value | Field value | Flexible, runtime cost |
| **AnonACSet** | Type parameter | Type parameter | Works with any schema |

---

## DeepWiki Integration (Verified 2025-12-22)

| DeepWiki Query | ACSets Skill | Match |
|----------------|--------------|-------|
| "ACSet = functor from schema to Set" | `C-set = Functor X: C → Set` | ✓ |
| "StructACSet uses type parameters" | Column storage + PT | ✓ |
| "Index optimizes incident queries" | O(1) via StoredPreimageCache | ✓ |
| "IntParts uses pop-and-swap" | Part ID allocation strategies | ✓ |

### Cross-Skill Synergy

```julia
# DeepWiki query → ACSet implementation → Spectral analysis
mcp__deepwiki__ask_question("AlgebraicJulia/ACSets.jl", 
    "How does incident query work with indices?")

# Answer: StoredPreimageCache maintains Dict{Int, Vector{Int}}
# Apply: incident(G, v, :src) retrieves precomputed edge list

# Combine with Ramanujan edge growth
grow_edge_ramanujan!(G, u, v)  # Uses add_part!, incident, rem_part!
```

---

## Related

- **Catlab.jl**: Homomorphisms, limits, colimits
- **StructuredDecompositions.jl**: ∫G, 𝐃 functor, FPT
- **AlgebraicDynamics.jl**: Wiring diagrams, oapply
- **SpecterOptimized.jl**: Zero-overhead navigation
- **ramanujan-expander**: Alon-Boppana spectral bounds
- **ihara-zeta**: Non-backtracking walks and zeta functions
- **moebius-inversion**: Alternating sums on posets
- **deepwiki-mcp**: Repository documentation (trit 0, substitutes in triads)
>>>>>>> origin/feature/skill-connectivity-hub-20251226
