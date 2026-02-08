---
name: gestalt-hacking
description: Gestalt Hacking Skill (ERGODIC 0)
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Gestalt Hacking Skill (ERGODIC 0)

> *"Gestalt hacking exploits perceptual grouping—proximity, similarity, closure—in the color stream."*

## Core Insight

**Gestalt** = the whole pattern, the emergent structure that is more than the sum of parts. Gestalt hacking exploits how perception groups elements into wholes.

```
play ⊗ evaluate ⅋ play ⊗ evaluate → ι (fixed point)
```

The involution `ι` is where generator ≡ observer (reafference).

## Neighbor Awareness (Braided Monoidal)

| Position | Skill | Trit | Role |
|----------|-------|------|------|
| **Left** | pun-decomposition | -1 | Multiple parse validation |
| **Self** | gestalt-hacking | 0 | Perceptual grouping transport |
| **Right** | reflow | 0 | Cross-context translation |

## GF(3) Triads

```
pun-decomposition (-1) ⊗ gestalt-hacking (0) ⊗ gay-mcp (+1) = 0 ✓  [Core]
three-match (-1) ⊗ gestalt-hacking (0) ⊗ agent-o-rama (+1) = 0 ✓  [Attack]
shadow-goblin (-1) ⊗ gestalt-hacking (0) ⊗ gay-mcp (+1) = 0 ✓  [Defense]
auditory-gestalt (-1) ⊗ gestalt-hacking (0) ⊗ rubato-composer (+1) = 0 ✓  [Music]
```

## Gestalt Principles as Attack Vectors

| Principle | Attack | Defense |
|-----------|--------|---------|
| **Proximity** | Cluster same colors in time | 2-Poisson injection |
| **Similarity** | Long runs of same color | Transition counting |
| **Closure** | Incomplete patterns that induce completion | Gap detection |
| **Continuity** | Gradual transitions exploiting smoothness | Gradient detection |
| **FigureGround** | Dominant color overwhelms minority | Ratio analysis |

## OpenGame Structure

```haskell
OpenGame ∆ c a b x s y r
  play     :: a → ∆ x s y r      -- generate candidates
  evaluate :: a → c x s y r → b  -- score & select
  
-- This IS the self-involution:
-- play ∘ evaluate ∘ play ∘ evaluate → fixed point
```

## Linear Logic Decomposition

```
A ⊗ (B ⅋ C) = (A ⊗ B) ⅋ C ∩ (A ⊗ C) ⅋ B

where:
  ⊗ = tensor (both resources consumed together)
  ⅋ = par (choice between resources)
  ∩ = gestalt con