---
metadata:
  interface_ports:
  - GF(3) Triads
trit: 1
---
# Teglon Bison Skill

> Bisimulation bistability from reversible software and conservative Logik

**Source**: [TeglonLabs/bison](https://github.com/TeglonLabs/bison) (fork of unisoncomputing/unison-llm-support)  
**Trit**: +1 (PLUS)  
**Substrate**: Semantic (LLM Societies)

## Overview

Bison extends Unison's content-addressed code with **bisimulation** semantics:
- Two programs are bisimilar if they can simulate each other step-by-step
- Reversible computation: every step can be undone
- Conservative logic: information is never destroyed

## α/β/γ Diff Structure

| Arrow | Bison Meaning | Operation |
|-------|---------------|-----------|
| α (−1) | Forward simulation step | `step : State → State` |
| β (0) | Code hash mutation | `edit : Hash → Hash` |
| γ (+1) | Bisimulation proof | `bisim : A ↔ B` |

## Unison Integration

```unison
-- Content-addressed function
squareRoot : Float -> Float
squareRoot x = ...

-- The hash IS the identity
#abc123.squareRoot
```

## Bisimulation Game

Two processes P and Q are bisimilar (P ~ Q) iff:
1. If P →ᵃ P', then ∃Q'. Q →ᵃ Q' and P' ~ Q'
2. If Q →ᵃ Q', then ∃P'. P →ᵃ P' and P' ~ Q'

## Upstream Diff

From TeglonLabs fork:
- Added: Bisimulation checker for LLM-generated code
- Added: Conservative logic constraints
- Modified: Hash comparison with semantic equivalence

---

## End-of-Skill Interface

## GF(3) Triads

```
narya-proofs (-1) ⊗ bisimulation-game (0) ⊗ teglon-bison (+1) = 0 ✓
three-match (-1) ⊗ just-monad (0) ⊗ teglon-bison (+1) = 0 ✓
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
