---
name: synthetic-adjunctions
description: Synthetic adjunctions in directed type theory for ∞-categorical universal
  constructions.
license: UNLICENSED
metadata:
  source: local
---

# Synthetic Adjunctions Skill: Universal Construction Generation

**Status**: ✅ Production Ready
**Trit**: +1 (PLUS - generator)
**Color**: #D82626 (Red)
**Principle**: Adjunctions generate universal structures
**Frame**: Directed type theory with adjoint functors

---

## Overview

**Synthetic Adjunctions** generates adjunction data in directed type theory. Adjunctions are the fundamental generators of universal constructions—limits, colimits, Kan extensions, and monads all arise from adjunctions.

1. **Unit/counit**: Natural transformations η, ε
2. **Triangle identities**: Coherence conditions
3. **Mate correspondence**: Bijection between hom-sets
4. **Universal properties**: Initial/terminal characterizations

## Core Formula

```
L ⊣ R adjunction:
  η : Id → R ∘ L       (unit)
  ε : L ∘ R → Id       (counit)
  
Triangle identities:
  (εL) ∘ (Lη) = id_L
  (Rε) ∘ (ηR) = id_R
```

```haskell
-- Generate adjunction from universal property
generate_adjunction :: FreeConstruction → Adjunction
generate_adjunction (Free F) = Adjunction {
    left = F,
    right = Forgetful,
    unit = η_universal,
    counit = ε_evaluation
}
```

## Key Concepts

### 1. Adjunction Generation

```agda
-- Construct adjunction from representability
representable-adjunction : 
  (F : A → B) → (G : B → A) →
  ((a : A) (b : B) → Hom_B(F a, b) ≃ Hom_A(a, G b)) →
  Adjunction F G
representable-adjunction F G iso = record
  { unit = λ a → iso.inv (id (F a))
  ; counit = λ b → iso.to (id (G b))
  ; triangle-L = from-iso-naturality
  ; triangle-R = from-iso-naturality
  }
```

### 2. Free-Forgetful Generation

```agda
-- Generate free algebra adjunction
free-forgetful : (T : Monad) → Adjunction (Free T) (Forgetful T)
free-forgetful T = record
  { unit = T.η
  ; counit = T.μ ∘ T.map(eval)
  ; triangle-L = T.left-unit
  ; triangle-R = T.right-unit
  }

-- Free monoid on sets
Free-Mon : Adjunction Free Underlying
Free-Mon = free-forgetful List-Monad
```

### 3. Kan Extension via Adjunction

```agda
-- Left Kan extension as left adjoint to restriction
Lan : (K : A → B) → Adjunction (Lan_K) (Res_K)
Lan K = record
  { left = λ F → colim_{K/b} F ∘ proj
  ; right = λ G → G ∘ K
  ; unit = universal-arrow
  ; counit = eval-at-colimit
  }
```

### 4. Generate Limits from Adjunctions

```agda
-- Diagonal adjunction gives limits
limit-adjunction : Adjunction Δ lim
limit-adjunction = record
  { left = Δ         -- diagonal functor
  ; right = lim      -- limit functor
  ; unit = proj      -- projections
  ; counit = univ    -- universal property
  }
```

## Commands

```bash
# Generate adjunction from free construction
just adjunction-generate --free-on Monoid

# Synthesize unit/counit
just adjunction-unit-counit L R

# Verify triangle identities
just adjunction-verify adj.rzk
```

## Integration with GF(3) Triads

```
covariant-fibrations (-1) ⊗ directed-interval (0) ⊗ synthetic-adjunctions (+1) = 0 ✓  [Transport]
yoneda-directed (-1) ⊗ elements-infinity-cats (0) ⊗ synthetic-adjunctions (+1) = 0 ✓  [Yoneda-Adjunction]
segal-types (-1) ⊗ directed-interval (0) ⊗ synthetic-adjunctions (+1) = 0 ✓  [Segal Adjunctions]
```

## Related Skills

- **elements-infinity-cats** (0): Coordinate ∞-categorical adjunctions
- **covariant-fibrations** (-1): Validate fibration conditions
- **free-monad-gen** (+1): Generate free monads from adjunctions

---

**Skill Name**: synthetic-adjunctions
**Type**: Universal Construction Generator
**Trit**: +1 (PLUS)
**Color**: #D82626 (Red)
