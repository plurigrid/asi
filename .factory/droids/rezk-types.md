---
name: rezk-types
description: "Rezk types (complete Segal spaces). Local univalence: categorical isomorphisms ≃ type-theoretic identities."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Rezk Types Skill

> *"In a Rezk type, isomorphisms are equivalent to identities — local univalence."*
> — Emily Riehl & Michael Shulman

## Overview

Rezk types are Segal types with an additional **local univalence** condition: categorical isomorphisms are equivalent to type-theoretic identities. This is the ∞-categorical analogue of the univalence axiom.

## Core Definitions (Rzk)

```rzk
#lang rzk-1

-- Isomorphism in a Segal type
#define is-iso (A : Segal) (x y : A) (f : hom A x y) : U
  := Σ (g : hom A y x), 
     (hom2 A x y x f g (id x)) × (hom2 A y x y g f (id y))

-- The type of isomorphisms
#define Iso (A : Segal) (x y : A) : U
  := Σ (f : hom A x y), is-iso A x y f

-- Identity-to-isomorphism map
#define id-to-iso (A : Segal) (x y : A) : (x = y) → Iso A x y
  := λ p. transport (λ z. Iso A x z) p (id x, refl-iso)

-- Rezk condition (local univalence)
#define is-rezk (A : Segal) : U
  := (x y : A) → is-equiv (id-to-iso A x y)

-- Rezk type (complete Segal space)
#define Rezk : U
  := Σ (A : Segal), is-rezk A
```

## Chemputer Semantics

| ∞-Category Concept | Chemical Interpretation |
|--------------------|------------------------|
| Isomorphism | Reversible reaction (equilibrium) |
| Local univalence | "Isomers at equilibrium are the same species" |
| Rezk completion | Finding thermodynamic fixed points |
| Identity = Iso | Chemical identity = equilibrium class |

## GF(3) Triad

```
segal-types (-1) ⊗ directed-interval (0) ⊗ rezk-types (+1) = 0 ✓
```

As a **Generator (+1)**, rezk-types creates:
- Complete categorical structure
- Univalent foundations for chemistry
- Equilibrium-respecting species identification

## The Local Univalence Principle

In a Rezk type:
```
(A ≅ B) ≃ (A = B)
```

**Chemical interpretation**: Two species at mutual equilibrium can be identified. The equilibrium constant K = 1 means "same species up to naming."

## Lean4 Integration

```lean
import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory

-- Rezk completion funct