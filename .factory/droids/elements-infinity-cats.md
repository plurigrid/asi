---
name: elements-infinity-cats
description: Elements of ∞-Category Theory (Riehl-Verity) for foundational ∞-categorical
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Elements of ∞-Categories Skill: Model-Independent Foundations

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - coordinator)
**Color**: #26D826 (Green)
**Principle**: ∞-categories via model-independent axioms
**Frame**: Riehl-Verity ∞-cosmos formalism

---

## Overview

**Elements of ∞-Category Theory** provides model-independent foundations for ∞-categories. Rather than committing to quasi-categories, complete Segal spaces, or another model, the ∞-cosmos framework captures the common structure.

1. **∞-cosmos**: Enriched category of ∞-categories
2. **Isofibrations**: Right class of factorization system
3. **Comma ∞-categories**: Slice constructions
4. **Adjunctions/equivalences**: Model-independent definitions

## Core Framework

```
∞-cosmos K has:
  - Objects: ∞-categories
  - Mapping spaces: Kan complexes Map_K(A, B)
  - Isofibrations: p : E ↠ B with lift property
  - Comma objects: A/f for f : A → B
```

```haskell
class InfinityCosmos k where
  type Ob k :: Type
  mapping :: Ob k → Ob k → KanComplex
  isofibration :: (e : Ob k) → (b : Ob k) → Prop
  comma :: {a b : Ob k} → (f : Map a b) → Ob k
```

## Key Concepts

### 1. ∞-Cosmos Structure

```agda
-- Core axioms of an ∞-cosmos
record ∞-Cosmos : Type₁ where
  field
    Ob : Type
    Hom : Ob → Ob → KanComplex
    id : (A : Ob) → Hom A A
    _∘_ : Hom B C → Hom A B → Hom A C
    
    -- Limits
    terminal : Ob
    product : Ob → Ob → Ob
    pullback : {A B C : Ob} → Hom A C → Hom B C → Ob
    
    -- Isofibrations
    isofib : {E B : Ob} → Hom E B → Prop
    factorization : (f : Hom A B) → 
      Σ E, Σ (p : Hom E B), isofib p × trivial-cofib(A → E)
```

### 2. Comma ∞-Categories

```agda
-- Comma construction
comma : {K : ∞-Cosmos} {A B C : K.Ob} 
      → K.Hom A C → K.Hom B C → K.Ob
comma f g = pullback (mapping-isofib A C f) (ev₀ : C^𝟚 → C) 
            ×_{C} pullback (mapping-isofib B C g) (ev₁ : C^𝟚 → C)

-- Slice as comma
slice : {K : ∞-Cosmos} (B : K.Ob) (b : pt → B) → K.Ob  
slice B b = comma