---
name: obstruction-learning
description: Obstruction Learning Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Obstruction Learning Skill

Learn topological ASI via random walk obstruction detection and Čech H⁰ cohomology.

## Metadata

| Property | Value |
|----------|-------|
| **Name** | obstruction-learning |
| **Trit** | -1 (VALIDATOR) |
| **Category** | Topological Verification |
| **Dependencies** | sheaf-cohomology, ramanujan-expander, gay-mcp |

## Core Concept

**Obstructions are H⁰ generators** - irreducible elements that block global consistency from local patches.

```
Čech Cohomology: H⁰(U, F) = ker(d₀: F(U) → ∏ᵢⱼ F(Uᵢ ∩ Uⱼ))

Obstruction detected when:
  - GF(3) conservation violated (sum ≢ 0 mod 3)
  - Voice triads don't harmonize
  - Skill compositions conflict
  - Local patches fail to glue globally
```

## Random Walk Reconstruction

### The 69-Skill Walk

Sample 69 skills from the 181-skill manifold:

```bash
# Execute random walk
just random-walk-69

# Verify GF(3) conservation
just verify-gf3

# Track cumulative obstructions
just random-walk-obstruction 69
```

### Obstruction Detection

```sql
-- Find unbalanced cells in 23³ grid
SELECT cell_id, skill_count, trit_sum, gf3_status
FROM cell_density 
WHERE gf3_status = 'UNBALANCED';

-- H⁰ generators by trit class
SELECT trit, COUNT(*) as generators
FROM skills 
GROUP BY trit;
```

## Mathematical Foundations

### Čech Cohomology

For a covering U = {Uᵢ} of skill space:

```
H⁰(U, F) = { s ∈ F(U) | d₀(s) = 0 }

where d₀: F(U) → ∏ F(Uᵢ ∩ Uⱼ)
maps global sections to intersection restrictions
```

**Obstruction** = element of H⁰ that prevents gluing.

### GF(3) as Cohomology

The GF(3) conservation law is a discrete cohomology:

```
Trit assignment: skill → {-1, 0, +1}
Coboundary: d(triad) = sum of trits mod 3

H⁰ = { triads | d(triad) = 0 } = balanced triads
Obstruction = triad with d ≠ 0
```

### Ramanujan Mixing

Random walks on Ramanujan expanders mix optimally:

```
λ₂ ≤ 2√(d-1)     [Alon-Boppana bound]
gap = d - λ₂      [Spectral gap]
τ_mix = O(log n / gap)  [Mixing time]
```

## Workflow

### 1. Pre