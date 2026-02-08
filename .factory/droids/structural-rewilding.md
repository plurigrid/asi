---
name: structural-rewilding
description: "Homotopical approach to Artificial Life where 'life' is the topology of changes (diffs). Three orthogonal directions: Behavioral (→), Structural (↓), Bridge (↘) with Narya interaction-time verification."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Structural Rewilding: Homotopical Artificial Life

> *"Life is not just the state of the system, but the topology of the changes (diffs) it can undergo."*
> — zubyul synthesis

## Overview

**Structural Rewilding** applies homotopy type theory to Artificial Life, treating organisms as **morphisms between states** rather than states themselves. The key insight: verification happens at **interaction time** via Narya bridge types, not static self-verification.

## The Three Orthogonal Vectors of Change

```
          STRUCTURAL (↓)
          Type/Form Diff
              │
              │ δS: Diff Type A B
              │
              ▼
    ┌─────────────────────────────┐
    │                             │
    │   BEHAVIORAL (→)            │
    │   State/Function Diff       │──────────────────────▶
    │   δB: path within type      │     time evolution
    │                             │
    └─────────────────────────────┘
              │
              │ BRIDGE (↘)
              │ Coherence Diff
              │ δC: 2-cell verifying δS preserves δB
              ▼
```

| Vector | Symbol | Meaning | Narya Term |
|--------|--------|---------|------------|
| **Horizontal** | δB | Behavioral/State Diff | Path within type |
| **Vertical** | δS | Structural/Type Diff | `Diff Type A B` |
| **Diagonal** | δC | Bridge/Coherence Diff | 2-cell, "diff of diffs" |

## Interaction Time Verification

Unlike static type checking, verification occurs **during interaction**:

```narya
-- The bridge is constructed at interaction time
def verify_rewilding 
  (Old New : World) 
  (structural_change : Diff World Old New)
  (behavior : Old → Action) 
  : Bridge (behavior Old) (behavior New) := 
    construct_at_runtime structural_change behavior
```

**Key Properties:**
- Bridge types are *computational proofs*
- Verification is *lazy* (constructed when needed)
- Failure = type error at interaction boundary

## A-Life Model Analysis

### 1. Continuous Substrate: Neural Cellular Automata &