# Graph Grafting Skill

**Trit**: 0 (ERGODIC - Coordinator)
**GF(3) Triad**: `queryable (-1) ⊗ graftable (0) ⊗ derangeable (+1) = 0`

## Overview

Combinatorial complex operations replacing GraphQL with pure graph theory:

| Operation | Trit | Description |
|-----------|------|-------------|
| **Queryable** | -1 | Tree-shape decision via bag decomposition |
| **Colorable** | 0 | GF(3) 3-coloring via sheaf |
| **Derangeable** | +1 | Permutations with no fixed points |
| **Graftable** | 0 | Attach rooted tree at vertex |

## Mathematical Foundation

**Grafting** = attaching a rooted tree T at vertex v of graph G:

```
Graft(T, v, G) → G' where:
  - V(G') = V(G) ∪ V(T)
  - E(G') = E(G) ∪ E(T) ∪ {(v, root(T))}
  - Adhesion = shared labels at attachment point
```

## Quadrant Chart: Colorable × Derangeable

```
        Balanced (GF3=0)
              │
    Q2        │        Q1 ← OPTIMAL
  Identity    │    PR#18, Knight Tour
              │    SICM Galois
──────────────┼──────────────
    Q3        │        Q4
  Deadlock    │    Phase Trans
              │
        Fixed Points → Derangement
```

## Usage

```julia
using .GraphGrafting

c = GraftComplex(UInt64(1069))

# Build PR tree
root = GraftNode(:pr18, Int8(0), :golden, 0)
alice = GraftNode(:alice, Int8(-1), :baseline, 1)
bob = GraftNode(:bob, Int8(1), :original, 1)

# Graft nodes
graft!(c, root, :none, String[])
graft!(c, alice, :pr18, ["aptos-wallet-mcp"])
graft!(c, bob, :pr18, ["aptos-wallet-mcp"])

# Operations
tree_shape(c)           # Queryable
trit_partition(c)       # Colorable  
derange!(c)             # Derangeable
compose(c1, c2, :vertex) # Graftable

# Verify
verify_gf3(c)  # → (conserved=true, sum=0)
```

## Neighbors

### High Affinity
- `three-match` (-1): Graph coloring verification
- `derangeable` (+1): No fixed points
- `bisimulation-game` (-1): Attacker/Defender

### Example Triad
```yaml
skills: [graph-grafting, three-match, derangeable]
sum: (0) + (-1) + (+1) = 0 ✓ CONSERVED
```

## References

- Joyal, Combinatorial Species (1981)
- Flajolet & Sedgewick, Analytic Combinatorics (2009)
- Topos Institute, Observational Bridge Types
