# Graded Monad Skill

> *"A graded monad is a lax 2-functor from a monoidal category (viewed as a one-object 2-category) to Cat."*
> — Soichiro Fujii (2019)

**Trit**: 0 (ERGODIC - coordinator)
**Color**: #26D826 (Green)
**Status**: Production Ready

---

## Overview

A **graded monad** (also called an **indexed monad** or **parametrized monad**) is a monad whose operations carry an index from a monoidal category. The 2-categorical perspective reveals graded monads as:

- **Lax 2-functors** from a monoidal category to Cat
- **Monads in a suitable 2-category** (Fujii's insight)
- **Effect systems** with tracked computational effects

This unifies the programming notion of graded effects with the categorical notion of 2-monads.

## Mathematical Definition

```
Given a monoidal category (M, ⊗, I):

A GRADED MONAD over M consists of:
  T : M → End(C)     (family of endofunctors indexed by M)
  η : Id → T_I       (unit, indexed by monoidal unit I)
  μ : T_m ∘ T_n → T_{m⊗n}  (multiplication, indexed by tensor)

subject to:
  μ_{m⊗n,p} ∘ (T_m μ_{n,p}) = μ_{m,n⊗p} ∘ (μ_{m,n} T_p)  (associativity)
  μ_{I,m} ∘ (η T_m) = id = μ_{m,I} ∘ (T_m η)                (unitality)

AS A 2-CATEGORICAL STRUCTURE:
  View M as a one-object 2-category ΣM:
    - One object: *
    - 1-cells: objects of M
    - 2-cells: morphisms of M
    - Composition: ⊗

  Then a graded monad = monad in the 2-category [ΣM, Cat]
  (lax 2-functors, lax natural transformations, modifications)

FUJII'S THEOREM:
  Graded monads over M ≅ Monads in Dist(M, -)
  where Dist is the 2-category of distributors/profunctors
```

## The 2-Categorical Connection

```
┌─────────────────────────────────────────────────────────────┐
│                                                             │
│   ORDINARY MONAD          GRADED MONAD                      │
│                                                             │
│   T : C → C               T_m : C → C  (for each m ∈ M)    │
│   η : Id → T              η : Id → T_I                     │
│   μ : T² → T              μ_{m,n} : T_m T_n → T_{m⊗n}     │
│                                                             │
│   = monad in Cat           = monad in [ΣM, Cat]             │
│   = 2-monad on 1           = 2-monad on ΣM                  │
│                                                             │
│   T-Alg = Eilenberg-       T-Alg = graded algebras          │
│           Moore cats                (effect handlers)        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

## GF(3) Mapping

| Concept | Trit | Role | Justification |
|---------|------|------|---------------|
| **Index category M** | -1 (MINUS) | Constraint | Constrains what grades are available |
| **Graded monad T** | 0 (ERGODIC) | Coordinator | Transports between graded effects |
| **Graded algebra** | +1 (PLUS) | Generator | Produces effect-aware computations |

The graded monad coordinates between the constraining index category and the generative algebras — hence trit 0.

## Programming Applications

### Effect Systems (Haskell)

```haskell
-- Graded monad for tracked effects
class GradedMonad (m :: k -> * -> *) where
  type Unit m :: k
  type Mult m (a :: k) (b :: k) :: k

  greturn :: a -> m (Unit m) a
  gbind   :: m i a -> (a -> m j b) -> m (Mult m i j) b

-- Example: State with tracked permissions
data Perm = Read | Write | ReadWrite

data StatePerm (p :: Perm) a where
  SRead  :: (s -> a) -> StatePerm 'Read a
  SWrite :: (s -> (a, s)) -> StatePerm 'Write a

instance GradedMonad StatePerm where
  type Unit StatePerm = 'Read
  type Mult StatePerm 'Read 'Read = 'Read
  type Mult StatePerm _ _ = 'Write  -- any write contaminates
```

### Algebraic Effects (Eff)

```
-- Graded by effect set
graded_run : {E : EffectSet} → Eff E a → Handler E a → a

-- Index tracks which effects are used
-- M = PowerSet(Effects) with ∪ as tensor
```

### IES Session Types (Lux Integration)

```
-- Session types are graded monads over protocol steps
Session : Protocol → Type → Type

-- Index category M = free category on protocol graph
-- T_step : action at that protocol step
-- μ : sequential composition of protocol steps
```

## Why This Skill Was Missing

Graded monads were **split** across adjacent concepts:

1. `free-monad-gen` generates free monads in 1-categories, not graded/indexed variants
2. `2-monad` defines 2-categorical monad theory but doesn't specialize to the ΣM case
3. `linear-logic` connects to resource tracking (grades ≈ resource annotations) but doesn't formalize the monad structure
4. `kan-extensions` handles Lan/Ran which can produce graded structure but doesn't own the definition

**Gap**: No skill connected the programming notion of graded effects (Haskell/Eff effect systems) to the 2-categorical definition (monads in [ΣM, Cat]). This unification is Fujii's key contribution and the bridge between 2-monad theory and practical programming.

## Julia/Catlab Integration

```julia
using Catlab.CategoricalAlgebra

@present SchGradedMonad(FreeSchema) begin
    # Index category M
    Grade::Ob
    GradeMorph::Ob
    grade_src::Hom(GradeMorph, Grade)
    grade_tgt::Hom(GradeMorph, Grade)

    # Monoidal structure on M
    tensor::Hom(Grade, Grade)  # m ⊗ n (simplified)
    unit_grade::Hom(Grade, Grade)  # I

    # Graded endofunctor family
    GradedEndo::Ob
    endo_grade::Hom(GradedEndo, Grade)  # T_m indexed by m

    # Multiplication indexed by grade pairs
    GradedMult::Ob
    mult_left::Hom(GradedMult, Grade)   # m
    mult_right::Hom(GradedMult, Grade)  # n
    mult_result::Hom(GradedMult, Grade) # m ⊗ n

    EffectLabel::AttrType
    grade_label::Attr(Grade, EffectLabel)
end
```

## Canonical Examples

| Index Category M | Graded Monad | Application |
|------------------|-------------|-------------|
| (ℕ, +, 0) | Bounded computation | Step-counting |
| ({R, W, RW}, ∪, ∅) | Permission tracking | Effect systems |
| (Protocol, ;, skip) | Session types | Distributed systems |
| (Cost, +, 0) | Resource usage | Linear types |
| (Latency, max, 0) | Timing bounds | Real-time systems |
| (GF(3), +, 0) | Trit-graded effects | GF(3) conservation! |

### GF(3) as Index Category

```
The GF(3) field itself is a monoidal category:
  Objects: {-1, 0, +1}
  Tensor: addition mod 3
  Unit: 0

A GF(3)-graded monad T tracks trit balance:
  T_{-1} : validator computations
  T_0    : coordinator computations
  T_{+1} : generator computations

  μ : T_m ∘ T_n → T_{m+n mod 3}

  Conservation: composing computations respects trit arithmetic
```

---

## Bidirectional Neighbor Index

### Edge-Scoped Propagator Table

| Edge | Direction | Scope | Fires When |
|------|-----------|-------|------------|
| graded-monad → 2-monad | outbound | `scope:compose` | Graded monad embedded as 2-monad |
| 2-monad → graded-monad | inbound | `scope:change` | Index category for grading identified |
| graded-monad → free-monad-gen | outbound | `scope:compose` | Free graded monad constructed |
| free-monad-gen → graded-monad | inbound | `scope:change` | Free monad specialized to graded |
| graded-monad → doctrinal-adjunction | outbound | `scope:change` | Index category adjunction needs doctrinal lift |
| doctrinal-adjunction → graded-monad | inbound | `scope:compose` | Graded monad arises from doctrinal adjunction |
| graded-monad → flexible-algebra | outbound | `scope:change` | Graded monad produces flexible algebras |
| flexible-algebra → graded-monad | inbound | `scope:compose` | Graded algebra flexibility checked |
| graded-monad → codescent | outbound | `scope:compose` | Graded monad strictified via codescent |
| codescent → graded-monad | inbound | `scope:verify` | Graded codescent checks index coherence |
| graded-monad → linear-logic | outbound | `scope:compose` | Resource grades = linear type annotations |
| linear-logic → graded-monad | inbound | `scope:change` | Linear resource tracking becomes graded monad |
| graded-monad → kan-extensions | outbound | `scope:compose` | Lan/Ran along index functor |
| kan-extensions → graded-monad | inbound | `scope:change` | Migration produces graded structure |
| graded-monad → open-games | outbound | `scope:compose` | Game effects graded by player |
| open-games → graded-monad | inbound | `scope:change` | Game composition produces graded monad |
| graded-monad → gf3-tripartite | outbound | `scope:verify` | GF(3) itself is index category |
| gf3-tripartite → graded-monad | inbound | `scope:compose` | Trit assignments form graded monad |
| graded-monad → lhott-cohesive-linear | outbound | `scope:compose` | Linear modality ♮ grades cohesion |
| lhott-cohesive-linear → graded-monad | inbound | `scope:change` | Cohesive modalities grade effects |

### Mutual Awareness Summary

```
       2-monad (0)
            ↑ compose
            │
free-monad (+1) ←── GRADED-MONAD (0) ──→ linear-logic (-1)
            │           │
            ↓ compose   ↓ verify
    codescent (-1)   gf3-tripartite (0)

+ 6 additional edges to existing skills
```

**Total edges**: 20 (10 bidirectional pairs)
**Propagator balance**: 6 scope:change + 8 scope:compose + 6 scope:verify = balanced

## GF(3) Triads

```
codescent (-1) ⊗ graded-monad (0) ⊗ flexible-algebra (+1) = 0 ✓  [Graded-BKP]
sheaf-cohomology (-1) ⊗ graded-monad (0) ⊗ free-monad-gen (+1) = 0 ✓  [Graded-Free]
linear-logic (-1) ⊗ graded-monad (0) ⊗ operad-compose (+1) = 0 ✓  [Resource-Operad]
segal-types (-1) ⊗ graded-monad (0) ⊗ synthetic-adjunctions (+1) = 0 ✓  [Index-Adjunction]
covariant-fibrations (-1) ⊗ graded-monad (0) ⊗ discopy-operads (+1) = 0 ✓  [Fibered-Graded]
```

## Commands

```bash
just graded-monad-define M           # Define graded monad over index M
just graded-monad-compose m n        # Compute μ_{m,n} : T_m T_n → T_{m⊗n}
just graded-monad-embed T            # Embed as 2-monad on ΣM
just graded-monad-effects program    # Track effect grades through program
just graded-monad-gf3 computation    # Verify GF(3) grade conservation
```

## References

- Fujii, S. (2019). "Towards a formal theory of graded monads." *FSCD* 4:1-17
- Katsumata, S. (2014). "Parametric effect monads and semantics of effect systems." *POPL*
- Orchard, D. & Yoshida, N. (2016). "Effects as sessions, sessions as effects." *POPL*
- Mellies, P.-A. (2017). "Categorical semantics of linear logic." In *Panoramas et Synthèses* 27
- Street, R. (1972). "The formal theory of monads." *JPAA* 2:149-168
- Smirnov, A. (2008). "Graded monads and rings of polynomials." *Journal of Homotopy and Related Structures*

## SDF Interleaving

### Primary Chapter: 6. Layering

**Concepts**: layered data, metadata, provenance, units

### GF(3) Balanced Triad

```
graded-monad (0) + SDF.Ch6 (0) + [balancer] (0) = 0
```

**Skill Trit**: 0 (ERGODIC - coordination)

### Connection Pattern

Layering adds metadata and provenance. Graded monads layer computational effects with grade annotations — each operation carries its "provenance" as an index from the grading category M.
