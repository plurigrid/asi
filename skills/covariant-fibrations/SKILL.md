---
name: covariant-fibrations
description: Riehl-Shulman covariant fibrations for dependent types over directed
  intervals in synthetic ∞-categories.
license: UNLICENSED
metadata:
  trit: -1
  source: local
geodesic: true
moebius: "μ(n) ≠ 0"
---

# Covariant Fibrations Skill: Directed Transport

**Status**: ✅ Production Ready
**Trit**: -1 (MINUS - validator/constraint)
**Color**: #2626D8 (Blue)
**Principle**: Type families respect directed morphisms
**Frame**: Covariant transport along 2-arrows

---

## Overview

**Covariant Fibrations** are type families B : A → U where transport goes *with* the direction of morphisms. In directed type theory, this ensures type families correctly propagate along the directed interval 𝟚.

1. **Directed interval 𝟚**: Type with 0 → 1 (not invertible)
2. **Covariant transport**: f : a → a' induces B(a) → B(a')
3. **Segal condition**: Composition witness for ∞-categories
4. **Fibration condition**: Lift existence (not uniqueness)

## Core Formula

```
For P : A → U covariant fibration:
  transport_P : (f : Hom_A(a, a')) → P(a) → P(a')
  
Covariance: transport respects composition
  transport_{g∘f} = transport_g ∘ transport_f
```

```haskell
-- Directed type theory (Narya-style)
covariant_fibration : (A : Type) → (P : A → Type) → Type
covariant_fibration A P = 
  (a a' : A) → (f : Hom A a a') → P a → P a'
```

## Key Concepts

### 1. Covariant Transport

```agda
-- Transport along directed morphisms
cov-transport : {A : Type} {P : A → Type} 
              → is-covariant P
              → {a a' : A} → Hom A a a' → P a → P a'
cov-transport cov f pa = cov.transport f pa

-- Functoriality
cov-comp : cov-transport (g ∘ f) ≡ cov-transport g ∘ cov-transport f
```

### 2. Cocartesian Lifts

```agda
-- Cocartesian lift characterizes covariant fibrations
is-cocartesian : {E B : Type} (p : E → B) 
               → {e : E} {b' : B} → Hom B (p e) b' → Type
is-cocartesian p {e} {b'} f = 
  Σ (e' : E), Σ (f̃ : Hom E e e'), (p f̃ ≡ f) × is-initial(f̃)
```

### 3. Segal Types with Covariance

```agda
-- Covariant families over Segal types
covariant-segal : (A : Segal) → (P : A → Type) → Type
covariant-segal A P = 
  (x y z : A) → (f : Hom x y) → (g : Hom y z) →
  cov-transport (g ∘ f) ≡ cov-transport g ∘ cov-transport f
```

## Commands

```bash
# Validate covariance conditions
just covariant-check fibration.rzk

# Compute cocartesian lifts
just cocartesian-lift base-morphism.rzk

# Generate transport terms
just cov-transport source target
```

## Integration with GF(3) Triads

```
covariant-fibrations (-1) ⊗ directed-interval (0) ⊗ synthetic-adjunctions (+1) = 0 ✓  [Transport]
covariant-fibrations (-1) ⊗ elements-infinity-cats (0) ⊗ rezk-types (+1) = 0 ✓  [∞-Fibrations]
```

## Related Skills

- **directed-interval** (0): Base directed type 𝟚
- **synthetic-adjunctions** (+1): Generate adjunctions from fibrations
- **segal-types** (-1): Validate Segal conditions

---

**Skill Name**: covariant-fibrations
**Type**: Directed Transport Validator
**Trit**: -1 (MINUS)
**Color**: #2626D8 (Blue)

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
