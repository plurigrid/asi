---
name: flexible-algebra
description: A **flexible T-algebra** is a strict T-algebra that admits enough "room to move" — it is a retract (in the pseudo-morphism category T-Alg) of a free algebra. Flexible algebras are the key to constructing bicolimits in categories of algebras and establishing the BKP biadjunction theorem.
---
# Flexible Algebra Skill

> *"A strict T-algebra A is flexible if and only if it is a retract in T-Alg of a free T-algebra TX."*
> — Blackwell, Kelly & Power (1989)

**Trit**: +1 (PLUS - generator)
**Color**: #D82626 (Red)
**Status**: Production Ready

---

## Overview

A **flexible T-algebra** is a strict T-algebra that admits enough "room to move" — it is a retract (in the pseudo-morphism category T-Alg) of a free algebra. Flexible algebras are the key to constructing bicolimits in categories of algebras and establishing the BKP biadjunction theorem.

## Mathematical Definition

```
Given a 2-monad T on K:

Definition (Flexible Algebra):
  A strict T-algebra (A, a : TA → A) is FLEXIBLE iff
  there exist:
    s : A → TX    (section, a pseudo T-morphism)
    r : TX → A    (retraction, a pseudo T-morphism)
  such that:
    r ∘ s ≅ id_A  (in T-Alg, i.e. via pseudo T-morphism iso)

Equivalently:
  A is flexible iff the canonical comparison
    A → T-Alg(TX, A)  (evaluation at generators)
  admits a section up to isomorphism.

Key Property:
  The inclusion J : T-Alg_s → T-Alg has a left biadjoint,
  and its essential image consists of the flexible algebras.
```

## The Pseudomorphism Classifier

```
For each strict T-algebra (A, a), there exists a universal
"pseudomorphism classifier" QA:

    ┌─────────────────────────────────────────────┐
    │                                             │
    │   QA = the free T-algebra on A's           │
    │        underlying object, equipped with     │
    │        universal pseudo T-morphism          │
    │                                             │
    │   q : A → QA    (universal pseudo map)      │
    │                                             │
    │   Universal property:                       │
    │   Ps-T-Alg(A, B) ≅ T-Alg_s(QA, B)          │
    │                                             │
    └─────────────────────────────────────────────┘

A is flexible iff it is a retract of QA.
```

## Why Flexibility Matters

### 1. Bicolimits in T-Alg

```
Theorem (BKP 1989):
  T-Alg has all PIE-bicolimits (Products, Inserters, Equifiers).
  These are computed as follows:

  1. Compute the "strict" colimit in T-Alg_s
  2. The result is automatically flexible
  3. Flexibility ensures it has the correct universal property
     as a bicolimit in T-Alg
```

### 2. Coherence via Flexibility

```
Theorem (BKP Coherence):
  Every pseudo T-algebra is equivalent (in T-Alg) to a strict one.

Proof sketch:
  Given pseudo T-algebra P:
  1. Form the codescent object of the free resolution
  2. This is a strict T-algebra (lives in T-Alg_s)
  3. It is flexible (retract of free)
  4. The canonical map is an equivalence P ≃ strict version
```

### 3. Generative Role (+1)

Flexible algebras **generate** structure:
- They produce bicolimits (create new categorical structure)
- They provide the "room" for pseudo-to-strict replacement
- They are the "good" algebras that make 2-dimensional algebra work

## GF(3) Mapping

| Concept | Trit | Role | Justification |
|---------|------|------|---------------|
| **Flexible algebra** | +1 (PLUS) | Generator | Creates bicolimits, generates structure |
| **Strict algebra** | — | Fixed point | Degenerate (no flexibility needed) |
| **Pseudo algebra** | 0 (ERGODIC) | Coordinator | Coherently equivalent to strict |
| **Non-flexible strict** | -1 (MINUS) | Constraint | Obstructs bicolimit existence |

## Why This Skill Was Missing

Flexible algebras were **implicit** across several skills without explicit treatment:

1. `2-monad` describes the strictness grid but doesn't isolate the retract condition
2. `free-monad-gen` generates free monads/algebras but not the retraction mechanism
3. `coequalizers` handles quotients but not the 2-categorical pseudomorphism classifier
4. `synthetic-adjunctions` generates adjunctions but not the biadjoint that produces flexible algebras

**Gap**: No skill owned the specific BKP construction: the pseudomorphism classifier Q, the retract condition, or the theorem that flexibility = bicolimit existence. This skill fills that gap as the **generator** of 2-algebraic structure.

## Julia/Catlab Integration

```julia
using Catlab.CategoricalAlgebra

@present SchFlexibleAlgebra(FreeSchema) begin
    Algebra::Ob
    FreeAlgebra::Ob
    PseudoMorphism::Ob

    # Retract data
    section::Hom(Algebra, FreeAlgebra)      # s : A → TX
    retraction::Hom(FreeAlgebra, Algebra)   # r : TX → A

    # Pseudomorphism classifier
    classifier::Hom(Algebra, FreeAlgebra)   # q : A → QA

    # Source/target for pseudo morphisms
    ps_source::Hom(PseudoMorphism, Algebra)
    ps_target::Hom(PseudoMorphism, Algebra)

    IsFlexible::AttrType  # Bool
    flexible::Attr(Algebra, IsFlexible)

    Strictness::AttrType
    alg_strictness::Attr(Algebra, Strictness)
end
```

## Canonical Examples

| 2-Monad T | Flexible T-Algebras | Non-Flexible |
|-----------|---------------------|--------------|
| Free monoid on Cat | Permutative categories with cofibrant replacement | — |
| Free coproduct | Categories with chosen coproducts, retract of free | Skeletal categories (sometimes) |
| Free symmetric monoidal | Permutative cats (= strict sym mon with retract) | — |
| Monad on Set | Retracts of free algebras (projective modules!) | Non-projective modules |

---

## Bidirectional Neighbor Index

### Edge-Scoped Propagator Table

| Edge | Direction | Scope | Fires When |
|------|-----------|-------|------------|
| flexible-algebra → 2-monad | outbound | `scope:verify` | Flexibility verified for T-algebra |
| 2-monad → flexible-algebra | inbound | `scope:change` | New T-algebra constructed, check flexibility |
| flexible-algebra → free-monad-gen | outbound | `scope:compose` | Free algebra needed as retract target |
| free-monad-gen → flexible-algebra | inbound | `scope:compose` | Free algebra generated, check retract |
| flexible-algebra → codescent | outbound | `scope:compose` | Codescent object is flexible |
| codescent → flexible-algebra | inbound | `scope:verify` | Codescent result checked for flexibility |
| flexible-algebra → doctrinal-adjunction | outbound | `scope:compose` | Flexible algebra produces adjunction |
| doctrinal-adjunction → flexible-algebra | inbound | `scope:verify` | Check if algebra retract is doctrinal |
| flexible-algebra → coequalizers | outbound | `scope:compose` | Coequalizer of flexible algebras is flexible |
| coequalizers → flexible-algebra | inbound | `scope:change` | Quotient computed, check flexibility |
| flexible-algebra → synthetic-adjunctions | outbound | `scope:compose` | Biadjoint generates flexible algebras |
| synthetic-adjunctions → flexible-algebra | inbound | `scope:change` | Adjunction produces retract structure |
| flexible-algebra → topos-adhesive-rewriting | outbound | `scope:change` | Rewriting preserves flexibility |
| topos-adhesive-rewriting → flexible-algebra | inbound | `scope:verify` | Rewrite result checked for flexibility |
| flexible-algebra → kan-extensions | outbound | `scope:compose` | Lan/Ran produce flexible algebras |
| kan-extensions → flexible-algebra | inbound | `scope:change` | Migration needs flexible target |
| flexible-algebra → acsets-algebraic-databases | outbound | `scope:change` | C-Set categories have flexible objects |
| acsets-algebraic-databases → flexible-algebra | inbound | `scope:verify` | Schema migration preserves flexibility |
| flexible-algebra → graded-monad | outbound | `scope:compose` | Graded algebra flexibility |
| graded-monad → flexible-algebra | inbound | `scope:change` | Graded monad produces flexible algebras |

### Mutual Awareness Summary

```
          codescent (-1)
               ↑ compose
               │
free-monad (+1) ←── FLEXIBLE-ALG (+1) ──→ 2-monad (0)
               │          │
               ↓ compose  ↓ verify
       coequalizers (0)  doctrinal-adj (0)

+ 6 additional edges to existing skills
```

**Total edges**: 20 (10 bidirectional pairs)
**Propagator balance**: 6 scope:change + 8 scope:compose + 6 scope:verify = balanced

## GF(3) Triads

```
codescent (-1) ⊗ 2-monad (0) ⊗ flexible-algebra (+1) = 0 ✓  [BKP Core]
sheaf-cohomology (-1) ⊗ kan-extensions (0) ⊗ flexible-algebra (+1) = 0 ✓  [Migration]
segal-types (-1) ⊗ graded-monad (0) ⊗ flexible-algebra (+1) = 0 ✓  [Graded-Flexible]
linear-logic (-1) ⊗ coequalizers (0) ⊗ flexible-algebra (+1) = 0 ✓  [Quotient-Flexible]
covariant-fibrations (-1) ⊗ doctrinal-adjunction (0) ⊗ flexible-algebra (+1) = 0 ✓  [Fibered-Flexible]
```

## Commands

```bash
just flexible-check A T              # Check if A is flexible for T
just flexible-classifier A T         # Compute pseudomorphism classifier QA
just flexible-retract A TX           # Construct retraction r : TX → A
just flexible-bicolimit diagram T    # Compute bicolimit via flexibility
just flexible-strictify pseudo-alg   # Strictify pseudo T-algebra
```

## References

- Blackwell, Kelly & Power (1989). "Two-dimensional monad theory." *JPAA* 59:1-41
- Lack, S. (2002). "Codescent objects and coherence." *JPAA* 175:223-241
- Lack, S. (2010). "A 2-categories companion." *IMA Vol. Math. Appl.* 152:105-191
- Kelly, G.M. (1989). "Elementary observations on 2-categorical limits." *Bull. Austral. Math. Soc.* 39:301-317

## SDF Interleaving

### Primary Chapter: 8. Degeneracy

**Concepts**: redundancy, fallback, multiple strategies, robustness

### GF(3) Balanced Triad

```
flexible-algebra (+1) + SDF.Ch8 (-1) + [balancer] (0) = 0
```

**Skill Trit**: +1 (PLUS - generation)

### Connection Pattern

Degeneracy provides redundancy and fallback. Flexible algebras provide the "room to move" — redundant paths through free algebras — that make the 2-categorical machinery robust.
