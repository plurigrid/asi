---
name: structured-decomp
description: "StructuredDecompositions.jl sheaves on tree decompositions for FPT algorithms with bidirectional navigation"
license: MIT
metadata:
  source: AlgebraicJulia/StructuredDecompositions.jl + music-topos
  trit: 0
  gf3_conserved: true
  version: 1.1.0
---

# Structured Decompositions Skill

> Sheaves on tree decompositions with bidirectional navigation

**Version**: 1.1.0
**Trit**: 0 (Ergodic - coordinates decomposition)

## Core Concept

**StrDecomp** = Functor `d: ∫G → C` where:
- **∫G** = category of elements of shape graph
- **C** = target category (Graph, FinSet, etc.)

```julia
using StructuredDecompositions

# Create decomposition from graph
d = StrDecomp(graph)

# Access components
bags(d)           # Local substructures
adhesions(d)      # Overlaps (shared boundaries)
adhesionSpans(d)  # Span morphisms
```

## The 𝐃 Functor

Lifts decision problems to decomposition space:

```julia
# Define problem as functor
k_coloring(G) = homomorphisms(G, K_k)

# Lift and solve
solution = 𝐃(k_coloring, decomp, CoDecomposition)
(answer, witness) = decide_sheaf_tree_shape(k_coloring, decomp)
```

## Specter-Style Navigation for Decompositions

Bidirectional paths for navigating decomposition structures:

```julia
using SpecterACSet

# Navigate bags
select([decomp_bags, ALL, acset_parts(:V)], decomp)

# Navigate adhesions with bidirectional transform
transform([decomp_adhesions, ALL], 
          adh -> reindex_adhesion(adh, mapping), 
          decomp)
```

### Decomposition Navigators

| Navigator | Select | Transform |
|-----------|--------|-----------|
| `decomp_bags` | All bag ACSets | Update bags |
| `decomp_adhesions` | All adhesion ACSets | Update adhesions |
| `decomp_spans` | Span morphisms | Reindex spans |
| `adhesion_between(i,j)` | Specific adhesion | Update specific |

## FPT Complexity

Runtime: **O(f(width) × n)** where width = max adhesion size

The sheaf condition ensures local solutions glue to global:

```julia
# Sheaf condition: sections over overlaps must agree
function verify_sheaf_condition(decomp, local_solutions)
    for (i, j) in adhesion_pairs(decomp)
        adh = adhesion(decomp, i, j)
        s_i = restrict(local_solutions[i], adh)
        s_j = restrict(local_solutions[j], adh)
        s_i == s_j || return false
    end
    return true
end
```

## Integration with lispsyntax-acset

Serialize decompositions to S-expressions for inspection:

```julia
# Decomposition → Sexp
sexp = sexp_of_strdecomp(decomp)

# Navigate sexp representation
bag_names = select([SEXP_CHILDREN, pred(is_bag), SEXP_HEAD, ATOM_VALUE], sexp)

# Roundtrip
decomp2 = strdecomp_of_sexp(GraphType, sexp)
```

## Adhesion as Colored Boundary

With Gay.jl deterministic coloring:

```julia
using Gay

struct ColoredAdhesion
    left_bag::ACSet
    right_bag::ACSet
    adhesion::ACSet
    color::String  # Deterministic from seed + index
end

function color_decomposition(decomp, seed)
    [ColoredAdhesion(
        bags(decomp)[i],
        bags(decomp)[j],
        adhesion(decomp, i, j),
        Gay.color_at(seed, idx)
    ) for (idx, (i, j)) in enumerate(adhesion_pairs(decomp))]
end
```

## GF(3) Triads

```
dmd-spectral (-1) ⊗ structured-decomp (0) ⊗ koopman-generator (+1) = 0 ✓
sheaf-cohomology (-1) ⊗ structured-decomp (0) ⊗ colimit-reconstruct (+1) = 0 ✓
```

## Time-Varying Data (Brunton + Spivak Integration)

For DMD/Koopman analysis on decomposed data:

```julia
@present SchTimeVaryingDecomp(FreeSchema) begin
    Interval::Ob
    Snapshot::Ob
    State::Ob
    
    timestamp::Hom(Snapshot, Interval)
    observable::Hom(Snapshot, State)
    
    Time::AttrType
    Value::AttrType
end

# Colimit reconstructs dynamics
# DMD = colimit of snapshot diagram over intervals
```

## References

- Bumpus et al. "Structured Decompositions" arXiv:2207.06091
- algebraicjulia.github.io/StructuredDecompositions.jl
- Nathan Marz: Specter inline caching patterns
