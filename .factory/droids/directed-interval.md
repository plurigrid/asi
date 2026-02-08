---
name: directed-interval
description: Directed interval type 2 axiomatizing (0 → 1). Time-directed homotopy
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Directed Interval Skill

> *"The directed interval 2 is the walking arrow: a single morphism 0 → 1."*
> — Riehl-Shulman

## Overview

The **directed interval 2** replaces the undirected interval 𝕀 of cubical type theory with a directed version. This axiomatizes the notion of "time flows forward" essential for modeling reactions.

## Core Definitions (Rzk)

```rzk
#lang rzk-1

-- CUBES: The category of directed cubes
-- 2 is the basic directed interval [0 → 1]

-- The directed interval (primitive)
#define 2 : CUBE

-- Endpoints
#define 0₂ : 2
#define 1₂ : 2

-- The unique arrow (built-in)
-- There is a morphism 0₂ → 1₂ but NOT 1₂ → 0₂

-- Higher cubes built from 2
#define 2×2 : CUBE := 2 × 2

-- Directed square (all arrows point same way)
#define □ : CUBE := 2 × 2

-- Simplex shapes
#define Δ¹ : CUBE := 2
#define Δ² : CUBE := { (t₁, t₂) : 2 × 2 | t₁ ≤ t₂ }
#define Δ³ : CUBE := { (t₁, t₂, t₃) : 2 × 2 × 2 | t₁ ≤ t₂ ∧ t₂ ≤ t₃ }

-- Hom type as extension type
#define hom (A : U) (x y : A) : U
  := { f : 2 → A | f 0₂ = x ∧ f 1₂ = y }
  -- equivalently: (t : 2) → A [t ≡ 0₂ ↦ x, t ≡ 1₂ ↦ y]
```

## Chemputer Semantics

| Directed Cube Concept | Chemical Interpretation |
|----------------------|------------------------|
| 2 (interval) | Reaction progress (0% → 100%) |
| 0₂ | Reactants (starting materials) |
| 1₂ | Products |
| hom A x y | Reaction pathway from x to y |
| Δ² | Two-step synthesis (A → B → C) |
| Δ³ | Three-step synthesis with associativity |
| □ (square) | Commuting reaction pathways |

## GF(3) Triad

```
segal-types (-1) ⊗ directed-interval (0) ⊗ rezk-types (+1) = 0 ✓
```

As a **Coordinator (0)**, directed-interval:
- Mediates between validators and generators
- Provides the "time axis" for computation
- Enables transport along directed paths

## Extension Types

The key innovation is **extension types** for partial elements:

```rzk
-- Extension type: functions with prescribed boundary
#define extension-type 
  (I : CUBE) (ψ : I → TOPE) (A : I → U) (a :