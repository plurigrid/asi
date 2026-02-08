---
name: ordered-locale
description: "Ordered Locales (Heunen-van der Schaaf 2024): Point-free topology with direction. Frame + compatible preorder with open cone conditions."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Ordered Locale Skill

> *"We extend Stone duality between topological spaces and locales to include order."*
> — Heunen & van der Schaaf, 2024

## Overview

An **ordered locale** is a locale (point-free topological space) equipped with a compatible preorder satisfying the **open cone condition**.

```
Ordered Locale = Frame + Preorder + Open Cones
```

## Key Definitions

### Frame (Locale)

A **frame** is a complete lattice where finite meets distribute over arbitrary joins:

```
a ∧ (⋁ᵢ bᵢ) = ⋁ᵢ (a ∧ bᵢ)
```

Equivalently: a complete Heyting algebra.

### Open Cone Condition

For a preorder ≤ on locale L, the **open cone condition** requires:

```
↑x = {y ∈ L : x ≤ y}  is an open in L  (upper cone)
↓x = {y ∈ L : y ≤ x}  is an open in L  (lower cone)
```

This ensures the order is "visible" to the topology.

### Ordered Locale (Definition 2.1, Heunen-van der Schaaf)

An **ordered locale** is a tuple (L, ≤) where:
1. L is a locale (frame of opens)
2. ≤ is a preorder on O(L)
3. The open cone condition holds

## Stone Duality Extended

```
┌────────────────────────┐     adjunction     ┌─────────────────────┐
│ Preordered Topological │ ←───────────────→ │   Ordered Locales   │
│ Spaces (open cones)    │                    │     (spatial)       │
└────────────────────────┘                    └─────────────────────┘
```

Restricts to an **equivalence**:
- Spatial ordered locales ≃ Sober T₀-ordered spaces with open cones

## Julia Implementation (Catlab.jl)

### Frame as Subobject Heyting Algebra

From Catlab's `Subobjects.jl`:

```julia
using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra

# Frame operations via ThSubobjectHeytingAlgebra
@signature ThFrame <: ThSubobjectHeytingAlgebra begin
  # Infinite joins (frame-specific)
  Join(I::TYPE, f::(I → Sub(X)))::Sub(X) ⊣ [X::Ob]
  
  # Frame distributivity: a ∧ (⋁ᵢ bᵢ) = ⋁ᵢ (a ∧ bᵢ)
end
```

### Ordered Locale Schema (ACSet)

```julia
using ACSets

@present SchOrderedLocale(FreeSchema) begin
  Open::Ob                