---
name: bumpus-narratives
description: Sheaves on time categories for compositional temporal reasoning. Bumpus
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Bumpus Narratives Skill

> **Trit**: 0 (ERGODIC) - Mediates between verification (-1) and generation (+1)

Sheaves on time categories for compositional reasoning about temporal data.

## Source Papers

- Bumpus, B.M. et al. "Unified Framework for Time-Varying Data" (arXiv:2402.00206)
- Bumpus, B.M. "Compositional Algorithms on Compositional Data" (arXiv:2302.05575)
- Bumpus, B.M. "Structured Decompositions" (arXiv:2207.06091)
- Bumpus, B.M. "Spined Categories" (arXiv:2104.01841)
- Bumpus, B.M. "Cohomological Obstructions" (arXiv:2408.15184)

## Core Concepts

### 1. Narratives as Sheaves

Temporal data = sheaf F: I_N → D where:
- I_N = time category (intervals [a,b] with inclusions)
- D = data category with pullbacks
- Sheaf condition: F([a,b]) = F([a,p]) ×_{F([p,p])} F([p,b])

```
F₁³ := {(x,y) ∈ F₁² × F₂³ | f₁,₂²(x) = f₂,₃²(y)}
```

### 2. Adhesion Filter (FPT Algorithm)

For tree decompositions of width w:
- Complexity: O(f(w) · n) instead of O(2^n)
- Runs on bag boundaries via pullback checking

```julia
function adhesion_filter(sheaf::Sheaf, decomp::TreeDecomp)
    for (bag1, bag2) in edges(decomp)
        adhesion = bag1 ∩ bag2
        if !is_pullback(sheaf, bag1, bag2, adhesion)
            return false
        end
    end
    true
end
```

### 3. Cohomological Obstructions

H⁰ detects local-to-global failure:
- H⁰(F) ≠ 0 → obstruction to gluing
- Čech complex on cover of intervals

## Integration with Gay.jl

### Color-Coded Narratives

Each interval [i,j] gets deterministic color:
```julia
color([i,j]) = gay_color(BUMPUS_SEED ⊻ hash(i,j))
```

### GF(3) Conservation

Narrative operations preserve triadic balance:
- **Restriction** (-1): F([a,b]) → F([a,a])
- **Extension** (+1): F([a,a]) → F([a,b])
- **Pullback** (0): F₁³ := fibered product

## Diagram Catalog

20 extracted diagrams from Bumpus papers:
- 17 commutative diagrams
- 2 functor diagrams
- 1 graph diagram

Location: `papers/diagrams/images/bumpus-*.jpg`

## Triadic Composition

```
structured-de