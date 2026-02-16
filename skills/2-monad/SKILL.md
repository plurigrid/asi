# 2-Monad Skill

> *"A 2-monad is a monad in the 2-category of 2-categories — the natural habitat of algebraic structure on categories."*
> — Blackwell, Kelly & Power (1989)

**Trit**: 0 (ERGODIC - coordinator)
**Color**: #26D826 (Green)
**Status**: Production Ready

---

## Overview

A **2-monad** is a monad internal to a 2-category K. Concretely, it consists of:

- An endo-2-functor `T : K → K`
- A 2-natural transformation `η : Id_K → T` (unit)
- A 2-natural transformation `μ : T² → T` (multiplication)
- Subject to the usual monad laws, now holding as equations between 2-natural transformations

The key insight: by varying the strictness of algebras and morphisms, a single 2-monad T generates a **4×4 grid of categories** T-Alg_s, Ps-T-Alg, Lax-T-Alg, Colax-T-Alg with strict/pseudo/lax/colax morphisms between them.

## Mathematical Definition

```
2-Monad (T, η, μ) on 2-category K:

  T : K → K           (endo-2-functor)
  η : Id → T          (unit, 2-natural)
  μ : TT → T          (multiplication, 2-natural)

  μ ∘ Tμ = μ ∘ μT     (associativity)
  μ ∘ Tη = id = μ ∘ ηT (unitality)
```

## The Strictness Grid

The central organizing principle of BKP theory:

```
                    MORPHISMS
              strict  pseudo  lax   colax
           ┌────────┬────────┬──────┬───────┐
  strict   │ T-Alg_s│ T-Alg  │ T-Algl│ T-Algc│
           ├────────┼────────┼──────┼───────┤
A pseudo   │ Ps-s   │ Ps-T   │ Ps-l │ Ps-c  │
L          ├────────┼────────┼──────┼───────┤
G lax      │ Lax-s  │ Lax-ps │Lax-l │ Lax-c │
S          ├────────┼────────┼──────┼───────┤
  colax    │ Col-s  │ Col-ps │Col-l │ Col-c │
           └────────┴────────┴──────┴───────┘

BKP Default: T-Alg = (strict algebras, pseudo morphisms)
             This is the "right" category for most purposes.
```

### GF(3) Mapping of Strictness

| Strictness | Trit | Role | Justification |
|------------|------|------|---------------|
| **Colax** | -1 (MINUS) | Validator | Weakens structure downward |
| **Pseudo** | 0 (ERGODIC) | Coordinator | Equivalence-invariant |
| **Lax** | +1 (PLUS) | Generator | Adds structure upward |
| **Strict** | — | Fixed point | Degenerate case (all trits equal) |

## Key Theorems (BKP 1989)

### 1. Biadjunction
```
The inclusion J : T-Alg_s → T-Alg has a left biadjoint.
Equivalently: T-Alg has all PIE-limits and J preserves them.
```

### 2. Flexible Algebras
```
A strict T-algebra A is flexible iff it is a retract (in T-Alg)
of a free T-algebra TX for some X.
```

### 3. Coherence
```
Every pseudo T-algebra is equivalent (in T-Alg) to a strict one.
"Pseudo = Strict up to equivalence"
```

## Canonical Examples

| 2-Monad T | K | T-Alg_s | T-Alg (pseudo) |
|-----------|---|---------|-----------------|
| Free monoid | Cat | Strict monoidal cats | Monoidal cats |
| Free coproduct | Cat | Cats with strict coproducts | Cats with coproducts |
| Free symmetric monoidal | Cat | Permutative cats | Symmetric monoidal cats |
| Idempotent completion | Cat | Cauchy-complete cats | Cauchy-complete cats |
| Presheaf construction | Cat^op | — | Topoi (as 2-algebras) |

## Julia/Catlab Integration

```julia
using Catlab.CategoricalAlgebra

# 2-Monad as endo-2-functor on Cat
@present Sch2Monad(FreeSchema) begin
    TwoCategory::Ob
    Algebra::Ob
    Morphism::Ob
    TwoCell::Ob

    alg_carrier::Hom(Algebra, TwoCategory)     # Underlying object
    alg_action::Hom(Algebra, Algebra)          # T-action
    mor_source::Hom(Morphism, Algebra)
    mor_target::Hom(Morphism, Algebra)
    cell_source::Hom(TwoCell, Morphism)
    cell_target::Hom(TwoCell, Morphism)

    Strictness::AttrType  # {-1, 0, +1} for colax/pseudo/lax
    alg_strictness::Attr(Algebra, Strictness)
    mor_strictness::Attr(Morphism, Strictness)
end
```

## Why This Skill Was Missing

The concept of 2-monads was **distributed across multiple skills** without a single owner:

1. `synthetic-adjunctions` handles adjunctions but not their monad-generating capacity in 2-categories
2. `kan-extensions` covers Lan/Ran but not the 2-monad T whose algebras are the extended structures
3. `infinity-operads` connects to operads-as-2-monads (Weber) but doesn't own the BKP theory
4. `free-monad-gen` generates free monads in 1-categories, not free 2-monads
5. `elements-infinity-cats` works at the ∞-level but doesn't specialize to strict 2-monads

**Gap**: No skill owned the strictness grid, the BKP biadjunction theorem, or the T-Alg construction. This skill fills that gap as the **central coordinator** for 2-categorical algebraic structure.

---

## Bidirectional Neighbor Index

### Edge-Scoped Propagator Table

| Edge | Direction | Scope | Fires When |
|------|-----------|-------|------------|
| 2-monad → doctrinal-adjunction | outbound | `scope:compose` | Adjunction between T-algebras formed |
| doctrinal-adjunction → 2-monad | inbound | `scope:change` | Lax/colax structure on adjoint discovered |
| 2-monad → flexible-algebra | outbound | `scope:change` | New T-algebra constructed |
| flexible-algebra → 2-monad | inbound | `scope:verify` | Flexibility of algebra verified |
| 2-monad → codescent | outbound | `scope:compose` | Pseudoalgebra needs strictification |
| codescent → 2-monad | inbound | `scope:verify` | Codescent object validates coherence |
| 2-monad → graded-monad | outbound | `scope:change` | Index category for grading identified |
| graded-monad → 2-monad | inbound | `scope:compose` | Graded monad embedded as 2-monad |
| 2-monad → synthetic-adjunctions | outbound | `scope:compose` | Monad extracted from adjunction |
| synthetic-adjunctions → 2-monad | inbound | `scope:change` | Adjunction L ⊣ R generates monad RL |
| 2-monad → kan-extensions | outbound | `scope:compose` | Lan/Ran gives 2-monad on presheaves |
| kan-extensions → 2-monad | inbound | `scope:change` | Migration via T-algebra structure |
| 2-monad → free-monad-gen | outbound | `scope:change` | Free T-algebra needed |
| free-monad-gen → 2-monad | inbound | `scope:compose` | Free monad lifted to 2-monad |
| 2-monad → infinity-operads | outbound | `scope:compose` | Operad realized as polynomial 2-monad |
| infinity-operads → 2-monad | inbound | `scope:change` | Dendroidal nerve of T-Alg |
| 2-monad → acsets-algebraic-databases | outbound | `scope:change` | C-Set categories are 2-monadic |
| acsets-algebraic-databases → 2-monad | inbound | `scope:verify` | Schema migration preserves T-structure |
| 2-monad → segal-types | outbound | `scope:verify` | Nerve of T-Alg is Segal |
| segal-types → 2-monad | inbound | `scope:verify` | Composition in T-Alg validated |
| 2-monad → open-games | outbound | `scope:compose` | Game composition via 2-monadic structure |
| open-games → 2-monad | inbound | `scope:change` | Para(Optic) as 2-monad algebra |
| 2-monad → bidirectional-lens-logic | outbound | `scope:change` | Lax/colax = covariant/contravariant |
| bidirectional-lens-logic → 2-monad | inbound | `scope:verify` | 4-kind lattice validates strictness grid |

### Mutual Awareness Summary

```
         codescent (-1)
              ↑ verify
              │
flexible (+1) ←── 2-MONAD (0) ──→ doctrinal-adj (0)
              │         │
              ↓ compose ↓ change
      graded (0)   synthetic-adj (+1)

+ 8 additional edges to existing skills
```

**Total edges**: 24 (12 bidirectional pairs)
**Propagator balance**: 8 scope:change + 8 scope:compose + 8 scope:verify = balanced

## GF(3) Triads

```
codescent (-1) ⊗ 2-monad (0) ⊗ flexible-algebra (+1) = 0 ✓  [BKP Core]
sheaf-cohomology (-1) ⊗ 2-monad (0) ⊗ synthetic-adjunctions (+1) = 0 ✓  [Adjunction-Monad]
segal-types (-1) ⊗ 2-monad (0) ⊗ free-monad-gen (+1) = 0 ✓  [Free-Forgetful]
linear-logic (-1) ⊗ 2-monad (0) ⊗ operad-compose (+1) = 0 ✓  [Resource-Algebraic]
covariant-fibrations (-1) ⊗ 2-monad (0) ⊗ discopy-operads (+1) = 0 ✓  [Fibered-Operadic]
```

## Commands

```bash
just 2-monad-grid              # Display full strictness grid
just 2-monad-algebras T        # List T-algebra categories
just 2-monad-from-adjunction L R  # Extract monad from adjunction
just 2-monad-coherence check   # Verify pseudo = strict up to equiv
just 2-monad-bkp-biadjoint T   # Compute BKP left biadjoint
```

## References

- Blackwell, Kelly & Power (1989). "Two-dimensional monad theory." *JPAA* 59:1-41
- Kelly (1974). "Doctrinal adjunction." *LNM* 420:257-280
- Lack (2002). "Codescent objects and coherence." *JPAA* 175:223-241
- Lack (2010). "A 2-categories companion." *IMA Vol. Math. Appl.* 152:105-191
- Weber (2015). "Operads as polynomial 2-monads." *TAC* 30:1659-1712
- Street (1972). "The formal theory of monads." *JPAA* 2:149-168

## SDF Interleaving

### Primary Chapter: 6. Layering

**Concepts**: layered data, metadata, provenance

### GF(3) Balanced Triad

```
2-monad (0) + SDF.Ch6 (0) + [balancer] (0) = 0
```

**Skill Trit**: 0 (ERGODIC - coordination)

### Connection Pattern

Layering adds structure level by level. 2-monads layer algebraic structure on categories, with each strictness level a new layer.
