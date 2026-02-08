---
name: naturality-factor
description: Naturality Factor Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Naturality Factor Skill

> *"The naturality condition ensures transformations commute with structure."*

Measures how well transformations preserve conservation laws across musical and categorical structures.

## Overview

**Trit**: 0 (ERGODIC - Coordinator)  
**Location**: `lib/conserved_quantity.rb`, `lib/rubato_bridge.rb`  
**Dependencies**: GF(3), Z/12Z chromatic, Rubato morphisms

## Core Concept

In category theory, a **natural transformation** η: F → G satisfies:

```
    η_A
F(A) ───→ G(A)
  │         │
F(f)       G(f)
  ↓         ↓
F(B) ───→ G(B)
    η_B
```

The **naturality factor** ν ∈ [0,1] measures how well this square commutes:
- ν = 1.0 → perfectly natural (conservation preserved)
- ν = 0.0 → maximally unnatural (conservation violated)

## Mazzola's Insight

From *Topos of Music*: "Conservation" in music IS naturality of functors. Transposition preserves intervals because the naturality square closes.

## Classes

### NaturalityFactor

```ruby
nf = ConservedQuantity::NaturalityFactor.new(
  conservation: ConservedQuantity::Laws::CHROMATIC,
  source_functor: ->(x) { x },
  target_functor: ->(x) { x }
)

result = nf.compute(
  eta: ->(x) { x + 7 },      # Transposition
  morphism: ->(x) { x },      # Identity morphism
  object_a: 60,               # C4
  object_b: 64                # E4
)
# => { factor: 1.0, defect: 0, natural?: true }
```

### Chromatic Naturality

```ruby
# Does transposition preserve intervals?
result = ConservedQuantity::NaturalityFactor.chromatic_naturality(
  interval: 7,           # Perfect fifth
  notes: [0, 4, 7]       # C major triad
)
# => { factor: 1.0, natural?: true, original_intervals: [4, 3] }
```

### Triadic Naturality (GF(3))

```ruby
# Does doubling preserve trit balance?
result = ConservedQuantity::NaturalityFactor.triadic_naturality(
  transform: ->(x) { x * 2 },
  objects: [0, 1, 2, 3, 4, 5],
  charge_fn: ->(x) { x % 3 }
)
# => { factor: 1.0, defect: 0, natural?: true }
```

### Yoneda Conservation

Objects det