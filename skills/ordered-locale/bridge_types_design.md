# Observational Bridge Type Theory for Ordered Locales

**Status**: Design Draft  
**ERGODIC Agent**: trit=0 (Coordinator)  
**Date**: 2024-12-24  
**References**: Heunen-van der Schaaf 2024, Riehl-Shulman 2017, Narya documentation

---

## Overview

This document designs an observational bridge type theory that models **ordered locales** from Heunen & van der Schaaf's 2024 work. The key insight is that **bridge types** in Narya (directed, asymmetric) correspond exactly to the **≪ order** on opens in an ordered locale.

```
Ordered Locale           ↔       Bridge Type Theory
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Frame L                  ↔       Type with complete lattice structure
Open U ∈ L               ↔       Proposition / Subtype
U ≪ V (way-below)        ↔       Bridge U V (directed path)
↑U (upward cone)         ↔       Dependent type family (covariant)
↓U (downward cone)       ↔       Dependent type family (contravariant)
Open cone condition      ↔       IsOpen (↑U) × IsOpen (↓U)
```

---

## 1. Frame as Type with Lattice Structure

### 1.1 Frame Type Signature

```narya
Frame : Type
Frame := {
  carrier : Type
  
  -- Complete lattice operations
  ⊥ : carrier
  ⊤ : carrier
  ∧ : carrier → carrier → carrier
  ∨ : carrier → carrier → carrier
  ⋁ : (I : Type) → (I → carrier) → carrier
  
  -- Frame distributivity law (∧ distributes over arbitrary ∨)
  distrib : (U : carrier) → (S : I → carrier) 
          → U ∧ (⋁ I S) = ⋁ I (λ i. U ∧ S i)
  
  -- Heyting implication (for complete Heyting algebra)
  ⇒ : carrier → carrier → carrier
  heyting-adj : (U V W : carrier) → (U ∧ V ≤ W) ↔ (U ≤ V ⇒ W)
}
```

### 1.2 Opens as Propositions

Opens in the locale are modeled as elements of the frame carrier, which we treat as propositions:

```narya
Open : Frame → Type
Open L := L.carrier

IsOpen : {L : Frame} → (U : Open L) → Prop
IsOpen U := Unit  -- All elements of the frame are by definition open
```

---

## 2. The ≪ Order as Bridge Types

### 2.1 Core Insight: Bridge ≠ Path

In HoTT, paths are symmetric: `Path A x y ≃ Path A y x`

In directed type theory (Narya), bridges are **asymmetric**:
- `Bridge A x y` does NOT imply `Bridge A y x`
- Bridges model the directed interval `𝟚 = {0 → 1}`

This matches the ≪ order on ordered locales:
- `U ≪ V` does NOT imply `V ≪ U`
- ≪ is the "way-below" relation: directional, not symmetric

### 2.2 Bridge Type for ≪

```narya
-- The way-below relation as a bridge type
_≪_ : {L : Frame} → Open L → Open L → Type
U ≪ V := Bridge (Open L) U V

-- Bridge formation (asymmetric directed path)
Bridge : (A : Type) → A → A → Type

-- Bridge types have:
--   reflexivity: refl : Bridge A x x
--   NO symmetry: Bridge A x y ↛ Bridge A y x
--   transitivity: comp : Bridge A x y → Bridge A y z → Bridge A x z
```

### 2.3 Properties of ≪ as Bridges

```narya
-- Reflexivity (every open is way-below itself in trivial sense)
≪-refl : (U : Open L) → U ≪ U
≪-refl U := refl

-- Transitivity (composition of bridges)
≪-trans : (U V W : Open L) → U ≪ V → V ≪ W → U ≪ W
≪-trans U V W b1 b2 := comp b1 b2

-- Compatibility with lattice (if U ≪ V then U ≤ V)
≪-implies-≤ : (U V : Open L) → U ≪ V → U ≤ V
≪-implies-≤ U V b := bridge-to-leq b

-- Interpolation property (characteristic of continuous frames)
≪-interpolate : (U V : Open L) → U ≪ V 
              → Σ (W : Open L). (U ≪ W) × (W ≪ V)
```

---

## 3. Open Cones as Type Families

### 3.1 Upward and Downward Cones

The upward cone ↑U = {V | U ≪ V} and downward cone ↓U = {V | V ≪ U}:

```narya
-- Upward cone: covariant family over bridges FROM U
↑_ : {L : Frame} → Open L → Type
↑ U := Σ (V : Open L). U ≪ V

-- Downward cone: contravariant family over bridges TO U  
↓_ : {L : Frame} → Open L → Type
↓ U := Σ (V : Open L). V ≪ U
```

### 3.2 Open Cone Condition as Dependent Type

The open cone condition from ordered locales: ↑U and ↓U must be open.

```narya
-- Open cone condition: both cones are themselves representable as opens
OpenConeCondition : {L : Frame} → (U : Open L) → Type
OpenConeCondition U := 
  Σ (up-open : Open L). (↑ U ≃ Σ (V : Open L). up-open ≤ V)
  × Σ (down-open : Open L). (↓ U ≃ Σ (V : Open L). V ≤ down-open)

-- Alternative formulation using IsOpen predicate
open-cone : (U : Open L) → IsOpen (↑ U) × IsOpen (↓ U)
```

### 3.3 Covariant Families (from Riehl-Shulman)

Following Rzk's `is-covariant` definition, type families over ordered locales:

```narya
-- A family C over opens is covariant if it has unique lifts
is-covariant : (L : Frame) → (C : Open L → Type) → Type
is-covariant L C := 
  (U V : Open L) → (b : U ≪ V) → (u : C U)
  → is-contr (Σ (v : C V). DHom b C u v)

-- Dependent hom over a bridge
DHom : {L : Frame} → {U V : Open L} → (b : U ≪ V) 
     → (C : Open L → Type) → C U → C V → Type
DHom b C u v := (t : 𝟚) → C (b t) [t ≡ 0 ↦ u, t ≡ 1 ↦ v]
```

---

## 4. GF(3) Conservation as Type Constraint

### 4.1 Trit Type

```narya
Trit : Type
Trit := {minus : -1, ergodic : 0, plus : +1}

-- GF(3) addition
_+₃_ : Trit → Trit → Trit
t1 +₃ t2 := mod3 (toInt t1 + toInt t2)
```

### 4.2 GF(3) Conservation Invariant

```narya
-- Conservation predicate: sum of trits ≡ 0 (mod 3)
GF3-conserved : (t₋₁ t₀ t₁ : Trit) → Prop
GF3-conserved t₋₁ t₀ t₁ := (t₋₁ +₃ t₀ +₃ t₁) = ergodic

-- As a dependent type (proof-carrying)
GF3-Triplet : Type
GF3-Triplet := Σ (t : Trit × Trit × Trit). GF3-conserved (fst t) (fst (snd t)) (snd (snd t))

-- Canonical balanced triplet
balanced : GF3-Triplet
balanced := ((minus, ergodic, plus), refl)
```

### 4.3 GF(3) on Ordered Locale Operations

```narya
-- Each locale operation preserves GF(3)
-- Meet is ERGODIC (0): neutral, combines
∧-trit : Trit
∧-trit := ergodic

-- Join is PLUS (+1): generative, creates
∨-trit : Trit  
∨-trit := plus

-- Implication is MINUS (-1): restrictive, constrains
⇒-trit : Trit
⇒-trit := minus

-- Conservation: ∧ + ∨ + ⇒ = 0 + 1 + (-1) = 0 ✓
locale-ops-conserved : GF3-conserved ∧-trit ∨-trit ⇒-trit
locale-ops-conserved := refl
```

---

## 5. Connection to Sheaves

### 5.1 Sections as Dependent Functions

Sheaves over a locale are modeled by type families where sections correspond to dependent functions:

```narya
-- A sheaf over L assigns types to opens
Sheaf : Frame → Type₁
Sheaf L := Open L → Type

-- Sections over U (elements of the sheaf at U)
Section : {L : Frame} → Sheaf L → Open L → Type
Section F U := F U

-- Restriction maps (from bridge/≪ structure)
restrict : {L : Frame} → (F : Sheaf L) → {U V : Open L} 
         → U ≪ V → F V → F U
restrict F b s := transport-bridge F (sym-bridge b) s
```

### 5.2 Descent as Bridge Coherence

The sheaf condition (descent) becomes coherence of dependent functions over bridges:

```narya
-- Descent data: compatible family over a cover
DescentData : {L : Frame} → (F : Sheaf L) → (cover : I → Open L) → Type
DescentData F cover := 
  Σ (local : (i : I) → F (cover i)).
    (i j : I) → (b : cover i ≪ cover j) 
    → DHom b F (local i) (local j)

-- Sheaf condition: descent data has unique gluing
is-sheaf : {L : Frame} → Sheaf L → Type
is-sheaf F := (U : Open L) → (cover : I → Open L) 
            → (⋁ I cover = U)
            → is-equiv (λ s. descent-map F cover s)
```

### 5.3 Directed Yoneda for Ordered Locales

```narya
-- Hom-presheaf for ordered locale
yoneda-open : {L : Frame} → Open L → Sheaf L
yoneda-open U V := V ≪ U

-- Directed Yoneda: sections ≃ elements
yoneda-lemma : {L : Frame} → (F : Sheaf L) → (U : Open L)
             → is-covariant L F
             → (Section F U) ≃ NatTrans (yoneda-open U) F
```

---

## 6. Narya Implementation Sketch

### 6.1 Basic Definitions

```narya
-- Using Narya's bridge type syntax
def OrderedLocale : Type := {
  L : Frame
  order : (U V : Open L) → Type  -- Bridge type
  cone-open : (U : Open L) → Prop  -- Open cone condition
  interpolation : (U V : Open L) → order U V 
                → Σ (W : Open L). (order U W) × (order W V)
}

-- The walking bridge (directed interval)
def 𝟚 : Type := data {
  | 0₂ : 𝟚
  | 1₂ : 𝟚
  | edge : Bridge 𝟚 0₂ 1₂
}

-- Opens form a Segal type (pre-∞-category) under ≪
def is-segal-opens : (L : OrderedLocale) → is-pre-∞-category (Open L.L)
is-segal-opens L := λ U V W f g.
  let composite := ≪-trans U V W f g
  in is-contr-pair composite (witness-comp f g composite)
```

### 6.2 Observational Equality for Opens

Using Narya's observational bridge types:

```narya
-- Diff type for opens (what does it mean to change an open?)
def Diff-Open : (L : Frame) → Open L → Open L → Type
Diff-Open L U V := Bridge (Open L) U V  -- Directed: U ≪ V

-- Reflexivity (null diff)
def refl-open : (U : Open L) → Diff-Open L U U
def refl-open U := refl

-- Merges as 2-dimensional bridges
def Merge-Open : (L : Frame) → (U₀₀ U₀₁ U₁₀ U₁₁ : Open L)
               → Diff-Open L U₀₀ U₀₁ → Diff-Open L U₀₀ U₁₀
               → Diff-Open L U₀₁ U₁₁ → Diff-Open L U₁₀ U₁₁
               → Type
Merge-Open L _ _ _ _ d₀ d₁ d₂ d₃ := 
  Bridge (Bridge (Open L)) d₀ d₁ d₂ d₃
```

---

## 7. Triadic Architecture

Following AGENTS.md resilience pattern:

| Role | Trit | Function in Ordered Locale |
|------|------|---------------------------|
| **MINUS (-1)** | Validator | Check cone openness, verify ≪ properties |
| **ERGODIC (0)** | Coordinator | Transport along bridges, sheaf descent |
| **PLUS (+1)** | Generator | Create joins, construct new opens |

```narya
-- Triadic processing of locale operations
def triadic-locale-op : (L : OrderedLocale) → (U V : Open L) → GF3-Triplet → Open L
triadic-locale-op L U V trits := match trits with
  | (minus, _, _) → U ⇒ V    -- Constrain: Heyting implication
  | (_, ergodic, _) → U ∧ V  -- Coordinate: meet
  | (_, _, plus) → U ∨ V     -- Generate: join
```

---

## 8. Summary

| Ordered Locale Concept | Bridge Type Theory | Type Signature |
|----------------------|-------------------|----------------|
| Frame L | Complete Heyting Algebra Type | `Frame : Type` |
| Open U | Element of frame | `Open L := L.carrier` |
| U ≪ V | Bridge type | `Bridge (Open L) U V` |
| ↑U | Covariant dependent sum | `Σ (V : Open L). U ≪ V` |
| ↓U | Contravariant dependent sum | `Σ (V : Open L). V ≪ U` |
| Open cone | Type family openness | `IsOpen (↑U) × IsOpen (↓U)` |
| Sheaf | Type family | `Open L → Type` |
| Section | Dependent function | `(U : Open L) → F U` |
| Descent | Bridge coherence | `DHom b F (local i) (local j)` |

---

## References

1. Heunen, C. & van der Schaaf, M. (2024). *Ordered Locales*
2. Riehl, E. & Shulman, M. (2017). *A type theory for synthetic ∞-categories*. Higher Structures 1(1), 147-224
3. Altenkirch, T. et al. (2024). *Internal parametricity, without an interval*
4. Myers, D.J. (2024). *Structure-aware version control via observational bridge types*. Topos Institute
5. Narya documentation: [Observational higher dimensions](https://narya.readthedocs.io/en/latest/observational.html)
6. Rzk proof assistant: [github.com/rzk-lang/rzk](https://github.com/rzk-lang/rzk)

---

**GF(3) Conservation**: This design preserves `Σ trits ≡ 0 (mod 3)` by:
- Frame ops: ∧(0) + ∨(+1) + ⇒(-1) = 0 ✓
- Triadic agents: MINUS(-1) + ERGODIC(0) + PLUS(+1) = 0 ✓
- Bridge directions: source(-1) + transport(0) + target(+1) = 0 ✓
