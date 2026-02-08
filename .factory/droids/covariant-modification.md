---
name: covariant-modification
description: Unified skill modification with covariant transport, Darwin Gödel Machine evolution, and MCP Tasks self-rewriting. GF(3) conserved.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Covariant Modification Skill

**Trit**: 0 (ERGODIC - coordinator)
**Color**: Green (#26D826)

## Overview

**Covariant Modification** unifies three skill patterns for safe, structure-preserving self-modification:

| Component Skill | Trit | Role | Pattern |
|-----------------|------|------|---------|
| `codex-self-rewriting` | +1 | Generator | Lisp-machine self-modification via MCP Tasks |
| `self-evolving-agent` | 0 | Coordinator | Darwin Gödel Machine evolution loops |
| `covariant-fibrations` | -1 | Validator | Type families respect directed morphisms |

**GF(3)**: (+1) + (0) + (-1) = 0 ✓

## Core Concept: Covariant Transport

When skill `A` modifies itself, dependent skills `B` must transform **covariantly**:

```
                    modify_A
        Skill_A ─────────────→ Skill_A'
           │                      │
    uses   │    COVARIANT        │ uses'
           │    TRANSPORT        │
           ↓                      ↓
        Skill_B ─────────────→ Skill_B'
                  transport_f
```

### Agda Definition

```agda
-- Skill fibration over dependency base
skill-fibration : (Base : SkillGraph) → (Fiber : Base → SkillVersion) → Type

-- Covariant transport along modification morphisms
cov-transport : {A A' : Skill} {P : SkillDeps A → Type}
              → (f : Modification A A')
              → P (deps A) → P (deps A')

-- Functoriality
cov-comp : ∀ (f : Mod A A') (g : Mod A' A'') →
           cov-transport (g ∘ f) ≡ cov-transport g ∘ cov-transport f
```

## MCP Tasks State Machine

From `codex-self-rewriting`:

```
                    ┌─────────────┐
                    │   working   │ LIVE (+1)
                    │   (modify)  │
                    └──────┬──────┘
                           │
              ┌────────────┼────────────┐
              ↓            ↓            ↓
    ┌─────────────┐ ┌─────────────┐ ┌─────────────┐
    │  completed  │ │input_required│ │   failed    │
    │ BACKFILL(-1)│ │  VERIFY (0) │ │ BACKFILL(-1)│
    └────────────