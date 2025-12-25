# Ordered Locales in Rzk

A formalization of ordered locales following Heunen-van der Schaaf (2024).
This literate Rzk file encodes frames (complete Heyting algebras), 
open cone conditions, and the triadic GF(3) structure.

```rzk
#lang rzk-1
```

## Preliminaries

We work with the directed interval cube `2` with endpoints `0₂` and `1₂`.
The universe `U` contains our types.

### Basic Type Constructors

```rzk
#define prod
  ( A B : U)
  : U
  := Σ (_ : A) , B

#define total-type
  ( A : U)
  ( B : A → U)
  : U
  := Σ (a : A) , B a
```

## Frames as Complete Heyting Algebras

A frame `O` is a complete lattice with distributive binary meets over arbitrary joins.
We axiomatize this via a carrier type and operations.

### Frame Structure

```rzk
#postulate Frame
  : U

#postulate carrier
  : Frame → U

#postulate meet
  ( F : Frame)
  : carrier F → carrier F → carrier F

#postulate join
  ( F : Frame)
  : carrier F → carrier F → carrier F

#postulate top
  ( F : Frame)
  : carrier F

#postulate bot
  ( F : Frame)
  : carrier F
```

### Frame Order

The partial order on frame elements: `a ≤ b` iff `a ∧ b = a`.

```rzk
#postulate frame-leq
  ( F : Frame)
  ( a b : carrier F)
  : U

#postulate leq-refl
  ( F : Frame)
  ( a : carrier F)
  : frame-leq F a a

#postulate leq-antisym
  ( F : Frame)
  ( a b : carrier F)
  ( p : frame-leq F a b)
  ( q : frame-leq F b a)
  : a =_{carrier F} b

#postulate leq-trans
  ( F : Frame)
  ( a b c : carrier F)
  ( p : frame-leq F a b)
  ( q : frame-leq F b c)
  : frame-leq F a c
```

### Frame Distributivity

The key frame axiom: `a ∧ (⋁ᵢ bᵢ) = ⋁ᵢ (a ∧ bᵢ)`.
We express this for binary joins; infinite joins require indexed families.

```rzk
#postulate frame-distrib
  ( F : Frame)
  ( a b c : carrier F)
  : meet F a (join F b c) =_{carrier F} join F (meet F a b) (meet F a c)
```

### Order Compatibility

Order is compatible with meets: `U ≤ V` implies `U ∧ W ≤ V ∧ W`.

```rzk
#postulate order-compat-meet
  ( F : Frame)
  ( u v w : carrier F)
  ( p : frame-leq F u v)
  : frame-leq F (meet F u w) (meet F v w)
```

## Directed Interval and Arrows

The directed interval `2` has endpoints `0₂` and `1₂`.
Order arrows model the causal structure.

### Order Arrow Type

An order arrow in frame F captures directed paths.

```rzk
#define OrderArrow
  ( F : Frame)
  : U
  := 2 → carrier F
```

### Boundary Conditions

Extract source and target from an order arrow.

```rzk
#define source
  ( F : Frame)
  ( f : OrderArrow F)
  : carrier F
  := f 0₂

#define target
  ( F : Frame)
  ( f : OrderArrow F)
  : carrier F
  := f 1₂
```

## Open Cone Conditions

The open cone condition requires that upper sets ↑x and lower sets ↓x are opens.

### Up-set Predicate

For `x : carrier F`, the up-set `↑x = {y | x ≤ y}` must be an open.

```rzk
#define is-upclosed
  ( F : Frame)
  ( P : carrier F → U)
  : U
  := (x y : carrier F) → frame-leq F x y → P x → P y

#postulate UpSet
  ( F : Frame)
  ( x : carrier F)
  : carrier F → U

#postulate upset-contains-base
  ( F : Frame)
  ( x : carrier F)
  : UpSet F x x

#postulate upset-is-upclosed
  ( F : Frame)
  ( x : carrier F)
  : is-upclosed F (UpSet F x)
```

### Down-set Predicate

For `x : carrier F`, the down-set `↓x = {y | y ≤ x}` must be an open.

```rzk
#define is-downclosed
  ( F : Frame)
  ( P : carrier F → U)
  : U
  := (x y : carrier F) → frame-leq F y x → P x → P y

#postulate DownSet
  ( F : Frame)
  ( x : carrier F)
  : carrier F → U

#postulate downset-contains-base
  ( F : Frame)
  ( x : carrier F)
  : DownSet F x x

#postulate downset-is-downclosed
  ( F : Frame)
  ( x : carrier F)
  : is-downclosed F (DownSet F x)
```

### Open Cone Condition

The open cone condition: both ↑x and ↓x are representable opens.

```rzk
#postulate open-cone-up
  ( F : Frame)
  ( x : carrier F)
  : Σ (u : carrier F) , ((y : carrier F) → UpSet F x y → frame-leq F u y)

#postulate open-cone-down
  ( F : Frame)
  ( x : carrier F)
  : Σ (d : carrier F) , ((y : carrier F) → DownSet F x y → frame-leq F y d)
```

## Compatible Preorder

A preorder on F compatible with the frame structure.

```rzk
#postulate preorder
  ( F : Frame)
  ( a b : carrier F)
  : U

#postulate preorder-refl
  ( F : Frame)
  ( a : carrier F)
  : preorder F a a

#postulate preorder-trans
  ( F : Frame)
  ( a b c : carrier F)
  ( p : preorder F a b)
  ( q : preorder F b c)
  : preorder F a c

#postulate preorder-compat
  ( F : Frame)
  ( u v w : carrier F)
  ( p : preorder F u v)
  : preorder F (meet F u w) (meet F v w)
```

## Ordered Locale Structure

An ordered locale combines frame with compatible preorder and open cones.

```rzk
#define OrderedLocale
  : U
  := Σ (F : Frame)
     , Σ (_ : (x : carrier F) → Σ (u : carrier F) , ((y : carrier F) → UpSet F x y → frame-leq F u y))
       , (x : carrier F) → Σ (d : carrier F) , ((y : carrier F) → DownSet F x y → frame-leq F y d)
```

## Triadic Structure: MINUS / ERGODIC / PLUS

The GF(3) triadic decomposition of opens into three components.
This models the `-1, 0, +1` trit conservation.

### Trit Type

```rzk
#postulate Trit
  : U

#postulate MINUS
  : Trit

#postulate ERGODIC
  : Trit

#postulate PLUS
  : Trit

#postulate rec-Trit
  ( C : U)
  ( m e p : C)
  : Trit → C

#postulate rec-Trit-MINUS
  ( C : U)
  ( m e p : C)
  : rec-Trit C m e p MINUS =_{C} m

#postulate rec-Trit-ERGODIC
  ( C : U)
  ( m e p : C)
  : rec-Trit C m e p ERGODIC =_{C} e

#postulate rec-Trit-PLUS
  ( C : U)
  ( m e p : C)
  : rec-Trit C m e p PLUS =_{C} p
```

### Triadic Opens

A triadic open assigns a frame element to each trit.

```rzk
#define TriadicOpen
  ( F : Frame)
  : U
  := Trit → carrier F

#define mk-triadic
  ( F : Frame)
  ( m e p : carrier F)
  : TriadicOpen F
  := \ t → rec-Trit (carrier F) m e p t
```

### GF(3) Conservation

The sum of trits is conserved modulo 3.
We represent this as a balanced condition: the meet of all three is bottom.

```rzk
#define gf3-balanced
  ( F : Frame)
  ( tri : TriadicOpen F)
  : U
  := meet F (meet F (tri MINUS) (tri ERGODIC)) (tri PLUS) =_{carrier F} bot F
```

### Triadic Decomposition of Order Arrows

An order arrow decomposes into three parallel paths.

```rzk
#define TriadicArrow
  ( F : Frame)
  : U
  := Trit → OrderArrow F

#define triadic-source
  ( F : Frame)
  ( ta : TriadicArrow F)
  : TriadicOpen F
  := \ t → source F (ta t)

#define triadic-target
  ( F : Frame)
  ( ta : TriadicArrow F)
  : TriadicOpen F
  := \ t → target F (ta t)
```

## Homotopy Between Order Arrows

Two order arrows are homotopic if connected by a path in the arrow space.

```rzk
#define arrow-homotopy
  ( F : Frame)
  ( f g : OrderArrow F)
  : U
  := Σ (h : 2 → OrderArrow F)
     , prod (h 0₂ =_{OrderArrow F} f) (h 1₂ =_{OrderArrow F} g)
```

## Composable Arrows and Segal Condition

Two arrows are composable when the target of the first equals the source of the second.

```rzk
#define is-composable
  ( F : Frame)
  ( f g : OrderArrow F)
  : U
  := target F f =_{carrier F} source F g

#define ComposableArrowPair
  ( F : Frame)
  : U
  := Σ (f : OrderArrow F)
     , Σ (g : OrderArrow F)
       , is-composable F f g
```

## Summary

This formalization captures:

1. **Frames** as complete Heyting algebras with `meet`, `join`, `top`, `bot`
2. **Frame distributivity**: `a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)`
3. **Order compatibility**: `U ≤ V ⟹ U ∧ W ≤ V ∧ W`
4. **Open cone condition**: `↑x` and `↓x` are opens for all `x`
5. **Directed interval**: Using Rzk's built-in `2` with `0₂`, `1₂`
6. **Triadic structure**: MINUS/ERGODIC/PLUS with GF(3) conservation
7. **Order arrows**: Morphisms in the frame respecting direction

The key insight from Heunen-van der Schaaf is that ordered locales provide
a point-free topology compatible with causal structure, essential for
quantum mechanics and directed homotopy theory.
