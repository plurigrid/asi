---
name: moebius-inversion
description: "Möbius inversion on posets and lattices: alternating sums, chromatic polynomials, incidence algebras, and centrality predicates."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Möbius Inversion Skill

> *"The Möbius function inverts summation over divisors - the fundamental tool connecting local constraints to global structure."*

## bmorphism Contributions

> *"all is bidirectional"*
> — [@bmorphism](https://gist.github.com/bmorphism/ead83aec97dab7f581d49ddcb34a46d4), Play/Coplay gist

**Categorical Connection**: Möbius inversion on posets is the prototypical example of **adjunction** in category theory — ζ and μ form a zeta-Möbius pair where convolution is the composition operation. This connects to:
- **Incidence algebras** as categorical structures on posets
- **Bidirectional computation** — inversion recovers local from global
- **Chromatic polynomials** via ACSet bond lattices

**Plurigrid Integration**: The GF(3) trit system uses μ(3) = -1 (3 is prime) as the fundamental sign flip that creates the action-perception duality:
- Action trits: {-, 0, +}
- Perception trits: {+, 0, -} (Möbius-inverted)
- Double inversion: μ ∘ μ = identity

**Key Reference**:
- Rota (1964) — "On the Foundations of Combinatorial Theory I: Theory of Möbius Functions"

## Overview

Möbius inversion provides:

1. **Alternating sums** - Invert cumulative sums to get point values
2. **Chromatic polynomials** - Count colorings via bond lattice
3. **Incidence algebras** - Algebraic structure on posets
4. **Centrality predicates** - Validate node importance via inversion

## Classical Möbius Function

### Definition

For positive integers:

```
μ(n) = { 1      if n = 1
       { (-1)^k if n = p₁p₂...pₖ (k distinct primes)
       { 0      if n has squared prime factor
```

### Key Values

| n | μ(n) | Meaning |
|---|------|---------|
| 1 | 1 | Identity |
| 2 | -1 | Prime |
| **3** | **-1** | **Prime - key for GF(3)** |
| 4 | 0 | Squared (2²) |
| 5 | -1 | Prime |
| 6 | 1 | Two primes (2·3) |
| 12 | 0 | Has 2² |
| 30 | -1 | Three primes (2·3·5) |

### Implementation

```julia
function moebius(n)
    if n == 1
        return 1
    end
    
    # Factor n
    factors =