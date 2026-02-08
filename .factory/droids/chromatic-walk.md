---
name: chromatic-walk
description: 3 parallel agents explore codebase improvements via GF(3) balanced prime geodesics
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Chromatic Walk Skill

**Trit**: 0 (ERGODIC - navigates between generation and validation)  
**Coordinator Color**: #D06546 (burnt sienna, transport of earth)  
**Seed**: 1069 (0x42D)

---

## Overview

Chromatic Walk enables **3 parallel agents** to explore codebase improvements using GF(3)-balanced derivation chains. Each agent holds a trit polarity, and together they form a self-boiling triad.

Walks are **prime geodesics**: non-backtracking paths that are unambiguously traversable in p-adic number systems.

```
Generator (⊕)  ─────┐
                    ├──→  GF(3) = 0  ──→  Prime Geodesic
Coordinator (○) ────┤
                    │
Validator (⊖)  ─────┘
```

---

## The 3-Agent Structure

| Role | Trit | Color | Action | Responsibility |
|------|------|-------|--------|----------------|
| **Generator** | +1 | #D82626 (Red) | Create | Propose code changes, new patterns |
| **Coordinator** | 0 | #26D826 (Green) | Transport | Formalize structure, derive next seed |
| **Validator** | -1 | #2626D8 (Blue) | Verify | Check invariants, reduce to essence |

---

## Prime Geodesic Foundation

See [PRIME_GEODESICS.md](./PRIME_GEODESICS.md) for full mathematical foundation.

### Why Non-Backtracking?

| Property | Prime Path | Composite Path |
|----------|------------|----------------|
| Factorization | **Unique** | Multiple |
| p-adic valuation | **Well-defined** | Ambiguous |
| Möbius μ(n) | ≠ 0 | = 0 (filtered) |
| Ihara zeta | **Contributes** | Ignored |

**Key insight**: Chromatic walks are prime geodesics in derivation space, traversable unambiguously by zeta functions.

### Zeta Function Traversability

| Zeta | Domain | Primes |
|------|--------|--------|
| Riemann ζ(s) | ℤ | Prime numbers |
| Ihara ζ_G(u) | Graphs | Non-backtracking cycles |
| Dedekind ζ_K(s) | Number fields | Prime ideals |
| Selberg Z(s) | Manifolds | Prime geodesics |

---

## Seed Chaining Across Agents

Each agent derives its seed from the shared genesis, offset by the golden ratio:

```ruby
