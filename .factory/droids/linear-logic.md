---
name: linear-logic
description: Linear Logic Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# linear-logic Skill


> *"Every resource used exactly once. No copying. No discarding. Pure computation."*

## Overview

**Linear Logic** implements Girard's linear logic for resource-aware computation. Linear types ensure resources are used exactly once, enabling safe concurrency and optimal memory management.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | -1 (MINUS) |
| Role | VALIDATOR |
| Function | Validates resource usage constraints |

## Connectives

```
┌─────────────────────────────────────────────────────────────────┐
│                    LINEAR LOGIC CONNECTIVES                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Multiplicative:              Additive:                        │
│                                                                 │
│  A ⊗ B  (tensor)              A ⊕ B  (plus/choice)             │
│  A ⅋ B  (par)                 A & B  (with/product)            │
│  1      (unit)                0      (zero)                    │
│  ⊥      (bottom)              ⊤      (top)                     │
│                                                                 │
│  Exponential:                 Negation:                        │
│                                                                 │
│  !A     (of course)           A⊥     (linear negation)         │
│  ?A     (why not)                                              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Resource Semantics

```haskell
-- Linear type: must be used exactly once
data Linear a where
    Use :: a -> Linear a

-- Consume: takes ownership, returns result
consume :: Linear a -> (a -> b) -> b
consume (Use x) f = f x

-- Cannot duplicate linear values!
-- duplicate :: Linear a -> (Linear a, Linear a)  -- FORBIDDEN

-- Cannot discard linear values!
-- 