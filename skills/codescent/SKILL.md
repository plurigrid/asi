---
name: codescent
description: 'A **codescent object** is the 2-categorical analogue of a coequalizer. While coequalizers identify elements under an equivalence relation, codescent objects identify 1-cells under a coherent system of 2-cells. They are the fundamental tool for:'
---
# Codescent Skill

> *"The codescent object of the simplicial bar resolution of a pseudoalgebra is a strict algebra equivalent to it."*
> — Steve Lack (2002)

**Trit**: -1 (MINUS - validator)
**Color**: #2626D8 (Blue)
**Status**: Production Ready

---

## Overview

A **codescent object** is the 2-categorical analogue of a coequalizer. While coequalizers identify elements under an equivalence relation, codescent objects identify 1-cells under a coherent system of 2-cells. They are the fundamental tool for:

1. **Strictifying** pseudo T-algebras to strict ones
2. **Computing bicolimits** in categories of T-algebras
3. **Verifying coherence** — checking that all diagrams involving associators and unitors commute

## Mathematical Definition

```
A codescent diagram is a truncated cosimplicial object:

    d₀            d₀           d₀
    →             →            →
  A ⇉ B  ⇛  C     (objects, 1-cells, 2-cells)
    →             →
    d₁            d₁

with 2-cells:
  σ₀ : d₁d₀ → d₀d₀   (face coherence)
  σ₁ : d₁d₁ → d₀d₁   (face coherence)
  τ  : d₀s₀ → id      (degeneracy coherence)

subject to cocycle conditions:
  σ₀(d₀) ∘ σ₁(d₀) = σ₀(d₁)  (cocycle)
  σ₀(s₀) = τ(d₀)             (normalization)
  σ₁(s₀) = τ(d₁)             (normalization)

The CODESCENT OBJECT is the 2-colimit of this data:
  Cods(A ⇉ B ⇛ C) = universal A equipped with
    q : B → Cods
    q ∘ d₀ = q ∘ d₁  (up to specified isomorphism)
    satisfying cocycle conditions
```

## Codescent vs Coequalizer

```
┌──────────────────────────────────────────────────────────────┐
│                                                              │
│  1-CATEGORICAL (Coequalizer):                                │
│                                                              │
│    X ⟹ Y → Q                                                │
│    f,g    q                                                  │
│                                                              │
│    q ∘ f = q ∘ g   (equality)                                │
│                                                              │
│  2-CATEGORICAL (Codescent):                                  │
│                                                              │
│    A ⇉ B ⇛ C → Cods                                         │
│         d₀,d₁  σ    q                                       │
│                                                              │
│    q ∘ d₀ ≅ q ∘ d₁   (isomorphism, not equality)            │
│    + coherence 2-cells satisfying cocycle conditions         │
│                                                              │
│  Key difference: codescent tracks WHY things are equal,      │
│  not just THAT they are equal.                               │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

## The Bar Resolution

The canonical source of codescent diagrams is the **bar resolution** of a pseudo T-algebra:

```
Given pseudo T-algebra (A, a, ā, ...):

  Bar resolution:
    T³A ⇛ T²A ⇉ TA → A

  where:
    d₀ = μA : T²A → TA       (multiplication)
    d₁ = Ta  : T²A → TA      (apply pseudo action)
    σ  = ā   : Ta ∘ μ → μ ∘ T²a  (associator 2-cell)

  Codescent of this = strict T-algebra equivalent to (A, a, ā)
```

## GF(3) Mapping

| Concept | Trit | Role | Justification |
|---------|------|------|---------------|
| **Codescent object** | -1 (MINUS) | Validator | Verifies coherence, constrains structure |
| **Bar resolution** | 0 (ERGODIC) | Coordinator | Produces the codescent diagram |
| **Strictification** | +1 (PLUS) | Generator | Output: strict algebra |

Codescent is fundamentally a **validation** operation: it checks whether coherence data (associators, unitors) satisfies the cocycle conditions, and produces the strictified result only when these conditions hold.

## Why This Skill Was Missing

Codescent was **partially covered** but not properly treated:

1. `coequalizers` handles 1-categorical quotients but not 2-dimensional codescent with its coherence 2-cells
2. `2-monad` describes the BKP theorems that use codescent but doesn't own the construction
3. `topos-adhesive-rewriting` uses pushouts and coequalizers for rewriting but at the 1-categorical level
4. `flexible-algebra` depends on codescent (flexibility = retract of codescent object) but doesn't construct it

**Gap**: No skill owned the 2-categorical colimit construction with its cocycle conditions, bar resolution input, and coherence verification. The `coequalizers` skill explicitly handles quotients by equivalence relations, but codescent handles quotients by **coherent systems of isomorphisms** — a strictly more refined operation.

## Julia/Catlab Integration

```julia
using Catlab.CategoricalAlgebra

@present SchCodescent(FreeSchema) begin
    # Truncated cosimplicial data
    Level0::Ob   # A
    Level1::Ob   # B
    Level2::Ob   # C
    TwoCell::Ob  # Coherence 2-cells

    # Face maps
    d0_01::Hom(Level0, Level1)   # d₀ : A → B
    d1_01::Hom(Level0, Level1)   # d₁ : A → B
    d0_12::Hom(Level1, Level2)   # d₀ : B → C
    d1_12::Hom(Level1, Level2)   # d₁ : B → C
    d2_12::Hom(Level1, Level2)   # d₂ : B → C

    # Degeneracy
    s0::Hom(Level1, Level0)      # s₀ : B → A

    # Coherence 2-cells (face/degeneracy coherence)
    sigma_source::Hom(TwoCell, Level2)
    sigma_target::Hom(TwoCell, Level2)

    # Codescent object
    CodescentObj::Ob
    cods_map::Hom(Level1, CodescentObj)  # q : B → Cods

    CocycleStatus::AttrType  # {satisfied, violated}
    cocycle::Attr(TwoCell, CocycleStatus)
end
```

## Canonical Examples

| Source | Codescent Diagram | Result |
|--------|-------------------|--------|
| Pseudo monoidal category | Bar(T³C ⇛ T²C ⇉ TC) | Strict monoidal (Mac Lane coherence) |
| Pseudo T-algebra | T³A ⇛ T²A ⇉ TA | Strict T-algebra (BKP coherence) |
| Descent data on sheaf | Čech nerve | Sheaf (glued section) |
| Homotopy colimit | Simplicial resolution | Colimit in model category |

---

## Bidirectional Neighbor Index

### Edge-Scoped Propagator Table

| Edge | Direction | Scope | Fires When |
|------|-----------|-------|------------|
| codescent → 2-monad | outbound | `scope:verify` | Codescent object validates coherence |
| 2-monad → codescent | inbound | `scope:compose` | Pseudoalgebra needs strictification |
| codescent → flexible-algebra | outbound | `scope:verify` | Codescent result checked for flexibility |
| flexible-algebra → codescent | inbound | `scope:compose` | Flexibility requires codescent construction |
| codescent → doctrinal-adjunction | outbound | `scope:verify` | Strictification confirms doctrinal structure |
| doctrinal-adjunction → codescent | inbound | `scope:verify` | Coherence of lift validated by codescent |
| codescent → coequalizers | outbound | `scope:change` | Codescent generalizes coequalizer to 2-dim |
| coequalizers → codescent | inbound | `scope:compose` | 1-categorical quotient lifts to codescent |
| codescent → sheaf-cohomology | outbound | `scope:verify` | Descent = dual of codescent |
| sheaf-cohomology → codescent | inbound | `scope:verify` | Čech cocycle = codescent cocycle |
| codescent → segal-types | outbound | `scope:verify` | Segal condition validated via codescent |
| segal-types → codescent | inbound | `scope:compose` | Segal type composition uses codescent |
| codescent → graded-monad | outbound | `scope:verify` | Graded codescent checks index coherence |
| graded-monad → codescent | inbound | `scope:compose` | Graded monad strictified via codescent |
| codescent → topos-adhesive-rewriting | outbound | `scope:compose` | Adhesive codescent for rewriting |
| topos-adhesive-rewriting → codescent | inbound | `scope:change` | Rewriting produces codescent data |
| codescent → infinity-operads | outbound | `scope:verify` | Dendroidal codescent |
| infinity-operads → codescent | inbound | `scope:compose` | ∞-operad algebras via codescent |
| codescent → elements-infinity-cats | outbound | `scope:verify` | ∞-categorical codescent |
| elements-infinity-cats → codescent | inbound | `scope:compose` | Model-independent codescent |

### Mutual Awareness Summary

```
         2-monad (0)
              ↑ verify
              │
coequalizers (0) ←── CODESCENT (-1) ──→ flexible-alg (+1)
              │           │
              ↓ verify    ↓ verify
      sheaf-coh (-1)  segal-types (-1)

+ 6 additional edges to existing skills
```

**Total edges**: 20 (10 bidirectional pairs)
**Propagator balance**: 4 scope:change + 8 scope:compose + 8 scope:verify = balanced (validator-heavy, appropriate for trit -1)

## GF(3) Triads

```
codescent (-1) ⊗ 2-monad (0) ⊗ flexible-algebra (+1) = 0 ✓  [BKP Core]
codescent (-1) ⊗ doctrinal-adjunction (0) ⊗ synthetic-adjunctions (+1) = 0 ✓  [Adjunction-Codescent]
codescent (-1) ⊗ kan-extensions (0) ⊗ free-monad-gen (+1) = 0 ✓  [Free-Codescent]
codescent (-1) ⊗ graded-monad (0) ⊗ operad-compose (+1) = 0 ✓  [Graded-Codescent]
codescent (-1) ⊗ elements-infinity-cats (0) ⊗ rezk-types (+1) = 0 ✓  [∞-Codescent]
```

## Commands

```bash
just codescent-compute diagram       # Compute codescent object
just codescent-bar T pseudo-alg      # Form bar resolution, compute codescent
just codescent-cocycle check         # Verify cocycle conditions
just codescent-strictify pseudo-alg  # Full strictification pipeline
just codescent-compare coeq codes    # Compare coequalizer vs codescent
```

## References

- Lack, S. (2002). "Codescent objects and coherence." *JPAA* 175:223-241
- Blackwell, Kelly & Power (1989). "Two-dimensional monad theory." *JPAA* 59:1-41
- Street, R. (1976). "Limits indexed by category-valued 2-functors." *JPAA* 8:149-181
- Lack, S. (2010). "A 2-categories companion." *IMA Vol. Math. Appl.* 152:105-191
- Power, J. (1989). "A general coherence result." *JPAA* 57:165-173

## SDF Interleaving

### Primary Chapter: 4. Pattern Matching

**Concepts**: unification, match, segment variables, pattern

### GF(3) Balanced Triad

```
codescent (-1) + SDF.Ch4 (+1) + [balancer] (0) = 0
```

**Skill Trit**: -1 (MINUS - verification)

### Connection Pattern

Pattern matching unifies structure. Codescent verifies that coherence patterns (cocycles) match — unifying pseudo-algebraic data into strict form via cocycle-checked descent.
