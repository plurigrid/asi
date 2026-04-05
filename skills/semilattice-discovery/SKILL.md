---
name: semilattice-discovery
description: Compositional skill discovery via join-semilattice fiber (color × trit × hash)
metadata:
  trit: 0
  bundle: core
  category: meta
---

# semilattice-discovery

> Find, compose, and verify skills using the free commutative idempotent semigroup.

**Trit**: 0 (Ergodic - coordinator)  
**Bundle**: core

## The Algebra

Every skill has a **SemilatticeFiber**: `{color, trit, hash}`.

- **hash**: `SplitMix64(name)` — deterministic, O(1)
- **trit**: `hash mod 3 - 1` ∈ {-1, 0, +1} — GF(3) conservation
- **color**: `hash → RGB → OKLAB` — perceptual similarity metric

Two skills compose via **fiber join**:
```
fiberJoin(a, b) = {
  color: OKLAB midpoint (idempotent, commutative)
  trit:  findBalancer(a.trit, b.trit)  — conserves GF(3)
  hash:  mix64(a.hash + b.hash)
}
```

## Commands

```bash
# Compute fiber for a skill
bb skill-semilattice.bb fiber bisimulation-game

# Join two skills — shows conservation
bb skill-semilattice.bb join bisimulation-game sheaf-cohomology

# Find the best third skill to complete a conserved triad
bb skill-semilattice.bb triad bisimulation-game sheaf-cohomology

# Discover skills by fiber proximity to a query
bb skill-semilattice.bb discover "color theory oklab"

# Verify global GF(3) conservation across all 1425 skills
bb skill-semilattice.bb conserved?

# Show skill clusters by trit and color proximity
bb skill-semilattice.bb cluster 5
```

## Semilattice Laws (verified)

| Law | Substrate | Braid | Color |
|-----|-----------|-------|-------|
| a ⊔ a = a | trit balancer idempotent | merge(v,v) = v | blend(c,c,0.5) = c |
| a ⊔ b = b ⊔ a | + is commutative | merge commutes | blend commutes |
| (a⊔b)⊔c = a⊔(b⊔c) | + is associative | merge associative | blend ≈ associative |

## Origin

Three independent discoveries of the same algebra:
- **Flavors** (Symbolics, 1979): mixin merge
- **CRDTs** (Kleppmann, 2011): state merge  
- **OKLAB** (Ottosson, 2020): perceptual blend

Jaffer's SLIB contains the three pieces (`colorspace.scm`, `modular.scm`, `random.scm`) never composed.
Gay.jl and `nanoclj-zig/src/semilattice.zig` are the first known compositions.

## Implementation

- **Zig**: `nanoclj-zig/src/semilattice.zig` (211 lines, 9 tests)
- **Babashka**: `asi/skill-semilattice.bb` (walks all 1425 skills)

## Results (2026-04-05)

```
Skills: 1425
Trit distribution: +1=478  0=481  -1=466
Trit sum: 12
GF(3) balanced: YES ✓ (sum mod 3 = 0)
```

## Related Skills

- `join-semilattice` — the abstract algebra
- `skill-dispatch` — GF(3) triadic task routing
- `gf3-conservation-oracle` — conservation verification
- `bisimulation-game` — behavioral equivalence
- `implicit-coordination` — stigmergic merge (distance 0.0000 from "semilattice crdt merge")
