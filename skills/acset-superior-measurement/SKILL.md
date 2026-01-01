---
name: acset-superior-measurement
description: Measure ACSets better than authors via surjectivity gadgets, Betti numbers,
  Möbius classification, and p-adic ultrametric distance
license: MIT
metadata:
  trit: 1
  color: '#DC789E'
  gf3_role: PLUS
  version: 1.0.0
  seed: 7449368709244611695
  interface_ports:
  - References
  - Integration with
---
# ACSet Superior Measurement

Quantitative analysis of ACSets beyond what AlgebraicJulia authors provide.

## GF(3) Triad

```
acset-superior-measurement (+1) ⊗ acsets-relational-thinking (0) ⊗ compositional-acset-comparison (-1) = 0 ✓
```

## The Gap We Fill

| Measurement | Authors | Us |
|-------------|---------|-----|
| **Surjectivity** | `incident()` | χ² coverage gadget |
| **Uniformity** | None | Statistical test |
| **Topology** | None | β₁ Betti number |
| **Paths** | Enumerate | Möbius classification |
| **Growth** | None | O(n)/O(n²)/O(n³) |
| **Distance** | None | P-adic ultrametric |

## Core Module

```julia
include("ACSetMeasurement.jl")
using .ACSetMeasurement

# Measure an ACSet
db = create_my_acset()
metrics = measure_acset(db)

# Check coverage
gadget = incident_coverage(db, :E, :V, :src)
println(gadget)  # Surjectivity(100→50, coverage=0.92, ✓ UNIFORM)

# P-adic distance between instances
d = padic_acset_distance(metrics_a, metrics_b, 3)
@assert verify_ultrametric(d_xy, d_yz, d_xz)  # Strong triangle
```

## Measurement Suite

### 1. Surjectivity Gadget

```julia
struct SurjectivityGadget
    n_source::Int           # |domain|
    n_target::Int           # |codomain|
    hit_counts::Vector{Int} # hits per target
    coverage::Float64       # fraction covered
    uniform::Bool           # χ² < threshold
    chi_squared::Float64    # statistic
end
```

### 2. Betti Numbers

```julia
β₁ = schema_betti_1(n_objects, n_morphisms, n_components)
# Independent cycles in schema graph
```

| Schema | β₁ | Meaning |
|--------|-----|---------|
| Tree | 0 | No cycles |
| Graph | 1 | src↔tgt cycle |
| INTERACTION | 4 | Highly connected |

### 3. Möbius Path Classification

```julia
classification = classify_paths(adjacency_matrix, max_length=4)
# classification.prime_paths   - μ > 0, clean
# classification.tangled_paths - μ ≤ 0, cyclic
# classification.ratio         - prime / total
```

### 4. Growth Rate Analysis

```julia
sizes = [measure_acset(build(n)).total_parts for n in [3, 9, 27]]
exponent, class = growth_rate_analysis(sizes, [3, 9, 27])
# class ∈ {"O(n)", "O(n²)", "O(n³)"}
```

### 5. P-Adic Ultrametric Distance

```julia
d = padic_acset_distance(metrics_a, metrics_b, p=3)
# Satisfies: d(x,z) ≤ max(d(x,y), d(y,z))
# Enables hierarchical clustering
```

## File Locations

- [ACSetMeasurement.jl](/Users/bob/ies/ACSetMeasurement.jl) - Julia implementation
- [ACSET_SUPERIOR_MEASUREMENT.md](/Users/bob/ies/ACSET_SUPERIOR_MEASUREMENT.md) - Theory & rationale
- [MaterializationGame.jl](/Users/bob/ies/MaterializationGame.jl#L622-L688) - incident_coverage origin

---

## End-of-Skill Interface

## Integration with Existing Skills

### From acsets-relational-thinking (0)
```julia
@present SchGraph(FreeSchema) begin
  V::Ob; E::Ob
  src::Hom(E, V); tgt::Hom(E, V)
end
@acset_type Graph(SchGraph)
```

### From compositional-acset-comparison (-1)
```julia
# DuckDB vs LanceDB schema comparison
geometric_morphism(duckdb_acset, lancedb_acset)
```

### This skill (+1)
```julia
# Measure quality of instances
metrics = measure_acset(db)
println(metrics.avg_coverage)      # How well morphisms cover
println(metrics.betti_1)           # Schema complexity
println(metrics.mobius_class.ratio) # Path quality
```

## References

- Bumpus et al. - Spasm counting for homomorphism enumeration
- AlgebraicJulia - Base ACSet implementation
- P-adic analysis - Ultrametric hierarchical clustering
