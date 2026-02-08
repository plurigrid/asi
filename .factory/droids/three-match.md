---
name: three-match
description: 3-MATCH colored subgraph isomorphism gadget for 3-SAT reduction
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

<!-- Propagated to amp | Trit: 0 | Source: .ruler/skills/three-match -->

# Three-Match Skill: 3-SAT via Colored Subgraph Isomorphism

**Status**: ✅ Production Ready
**Trit**: -1 (MINUS - conservative/geodesic)
**Principle**: Local constraints → Global correctness
**Frame**: Non-backtracking geodesics with Möbius filtering

---

## Overview

**Three-Match** reduces 3-SAT to 3-coloring which reduces to colored subgraph isomorphism. The 3-MATCH gadget enforces constraints LOCALLY via:

1. Non-backtracking geodesics (prime paths, μ(n) ≠ 0)
2. Möbius inversion filtering (back-and-forth cancellation)
3. GF(3) conservation (sum ≡ 0 mod 3)

**Correct by construction**: If local geodesic constraints are satisfied, global 3-SAT solution is guaranteed.

## Core Formula

```ruby
# Three colors match at depth d iff:
# - Pairwise differences have 3-adic valuation ≥ d
# - No backtracking (each color unique in path)
# - GF(3) sum ≡ 0 (mod 3)

v₃(|a - b|) ≥ d  ∧  v₃(|b - c|) ≥ d  ∧  v₃(|c - a|) ≥ d
```

## Why Non-Backtracking?

1. **Prime paths**: μ(n) ≠ 0 ⟺ n is squarefree
2. **No revisiting**: Each state appears once in geodesic
3. **Möbius filtering**: Composites (backtracking) cancel out
4. **Spectral gap**: Ramanujan property (λ₂ ≤ 2√(k-1))

## Gadgets

### 1. ThreeMatch Gadget

Three colors forming a valid local constraint:

```ruby
match = ThreeMatchGeodesicGadget::ThreeMatch.new(seed: 0x42D, depth: 1)
match.color_a  # => { trit: -1, hex: "#2626D8", polarity: :minus }
match.color_b  # => { trit: 0, hex: "#26D826", polarity: :ergodic }
match.color_c  # => { trit: 1, hex: "#D82626", polarity: :plus }
match.gf3_conserved?  # => true
```

### 2. NonBacktrackingGeodesic

Prime path through color space:

```ruby
geo = NonBacktrackingGeodesic.new(seed: seed, length: 8).generate!
geo.prime?           # => true (no backtracking)
geo.moebius_product  # => ±1 (non-zero for primes)
geo.moebius_filter   # => filtered path (only primes kept)
```

### 3. ColoredSubgraphGadget

3-SAT claus