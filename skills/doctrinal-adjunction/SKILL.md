# Doctrinal Adjunction Skill

> *"An adjunction between T-algebras is precisely a lax T-morphism structure on the right adjoint, equivalently a colax T-morphism structure on the left adjoint."*
> — G.M. Kelly (1974)

**Trit**: 0 (ERGODIC - coordinator)
**Color**: #26D826 (Green)
**Status**: Production Ready

---

## Overview

A **doctrinal adjunction** is Kelly's 1974 theorem establishing a canonical bijection between:

- **Lax T-morphism structures** on a right adjoint u : B → A
- **Colax T-morphism structures** on the left adjoint f : A → B

Given a 2-monad T on a 2-category K, and an adjunction f ⊣ u in K, the mate correspondence lifts the adjunction to the world of T-algebras in a canonical way.

## Mathematical Definition

```
Given:
  T = (T, η, μ)  a 2-monad on K
  (A, a) and (B, b)  strict T-algebras
  f ⊣ u : B → A  adjunction in K
  η_adj : 1 → uf   (unit)
  ε_adj : fu → 1   (counit)

Theorem (Kelly 1974):
  There is a bijection between:

  (i)  Lax T-morphism structures on u:
       ū : Tb ∘ Tu → u ∘ Ta   (lax cell)
       satisfying unit and associativity axioms

  (ii) Colax T-morphism structures on f:
       f̄ : f ∘ Ta → Tb ∘ Tf   (colax cell)
       satisfying unit and associativity axioms

  given by the mate correspondence:

       ū ↦ f̄ = (Tb ∘ Tε) ∘ (Tb ∘ T(ū) ∘ Tf) ∘ (Tη ∘ Tf)
       f̄ ↦ ū = (u ∘ Tε) ∘ (u ∘ T(f̄) ∘ Tu) ∘ (Tη ∘ Tu)
```

## The Mate Correspondence

The key mechanism is the **mate correspondence** for 2-cells under adjunctions:

```
Given f ⊣ u with unit η and counit ε:

  ┌─────────────────────────────────────────────────┐
  │                                                 │
  │   2-cells  α : gf → h     (in left variable)   │
  │            ↕  bijection                         │
  │   2-cells  ᾱ : g → hu     (in right variable)  │
  │                                                 │
  │   α ↦ ᾱ = (hε) ∘ (αu) ∘ (gη)                   │
  │   ᾱ ↦ α = (hε) ∘ (ᾱf)                          │
  │                                                 │
  └─────────────────────────────────────────────────┘
```

Applied to the T-algebra structure cells, this produces the lax↔colax bijection.

## GF(3) Mapping

| Structure | Trit | Role | Justification |
|-----------|------|------|---------------|
| **Colax T-morphism on f** | -1 (MINUS) | Validator | Weakens structure (colax) |
| **Mate correspondence** | 0 (ERGODIC) | Coordinator | Bijection itself |
| **Lax T-morphism on u** | +1 (PLUS) | Generator | Enriches structure (lax) |

The doctrinal adjunction is the **coordinator** that mediates between lax and colax — hence trit 0.

## Why This Skill Was Missing

The concept of doctrinal adjunction was **fragmented** across existing skills:

1. `synthetic-adjunctions` handles adjunctions but not the T-algebra lifting
2. `2-monad` defines the strictness grid but doesn't own the adjunction-lifting mechanism
3. `bidirectional-lens-logic` captures covariant/contravariant duality but not the specific Kelly bijection
4. `open-games` uses play/coplay (≈ lax/colax) but doesn't formalize the mate correspondence

**Gap**: No skill owned the canonical bijection between lax and colax T-morphism structures via mates, which is the mechanism that connects the GF(3) validator (-1, colax) to the generator (+1, lax) through the coordinator (0, mate).

## Julia/Catlab Integration

```julia
using Catlab.CategoricalAlgebra

@present SchDoctrinalAdj(FreeSchema) begin
    Algebra::Ob
    Adjunction::Ob
    LaxCell::Ob
    ColaxCell::Ob

    adj_left::Hom(Adjunction, Algebra)     # f : A → B
    adj_right::Hom(Adjunction, Algebra)    # u : B → A
    lax_source::Hom(LaxCell, Adjunction)
    colax_source::Hom(ColaxCell, Adjunction)

    # Mate correspondence as morphism
    mate_lax_to_colax::Hom(LaxCell, ColaxCell)
    mate_colax_to_lax::Hom(ColaxCell, LaxCell)

    Strictness::AttrType
    lax_strictness::Attr(LaxCell, Strictness)    # always +1
    colax_strictness::Attr(ColaxCell, Strictness) # always -1
end
```

## Canonical Examples

| Adjunction f ⊣ u | T-Monad | Lax on u | Colax on f |
|-------------------|---------|----------|------------|
| Free ⊣ Forgetful (monoids) | Free monoid | Monoid homomorphism | Oplax monoidal |
| Σ ⊣ Δ ⊣ Π (dependent) | — | Reindexing preserves | Pushforward weakens |
| L ⊣ R (Galois) | Closure | R preserves meets | L preserves joins |
| Parse ⊣ Synthesize (voice) | Music topos | Lax harmonic structure | Colax voice leading |

---

## Bidirectional Neighbor Index

### Edge-Scoped Propagator Table

| Edge | Direction | Scope | Fires When |
|------|-----------|-------|------------|
| doctrinal-adjunction → 2-monad | outbound | `scope:compose` | Adjunction lifts to T-Alg |
| 2-monad → doctrinal-adjunction | inbound | `scope:change` | New 2-monad defined, check adjunction lifting |
| doctrinal-adjunction → synthetic-adjunctions | outbound | `scope:compose` | Raw adjunction needs T-structure |
| synthetic-adjunctions → doctrinal-adjunction | inbound | `scope:change` | New adjunction generated |
| doctrinal-adjunction → flexible-algebra | outbound | `scope:verify` | Check if algebra retract is doctrinal |
| flexible-algebra → doctrinal-adjunction | inbound | `scope:compose` | Flexible algebra produces adjunction |
| doctrinal-adjunction → bidirectional-lens-logic | outbound | `scope:change` | Lax/colax mapped to covariant/contravariant |
| bidirectional-lens-logic → doctrinal-adjunction | inbound | `scope:verify` | 4-kind lattice validates mate correspondence |
| doctrinal-adjunction → open-games | outbound | `scope:compose` | Play/coplay lifted through T-Alg |
| open-games → doctrinal-adjunction | inbound | `scope:change` | Game equilibrium requires doctrinal lift |
| doctrinal-adjunction → kan-extensions | outbound | `scope:compose` | Lan ⊣ Res ⊣ Ran are doctrinal |
| kan-extensions → doctrinal-adjunction | inbound | `scope:change` | Kan extension adjunction discovered |
| doctrinal-adjunction → codescent | outbound | `scope:verify` | Codescent validates coherence of lift |
| codescent → doctrinal-adjunction | inbound | `scope:verify` | Strictification confirms doctrinal structure |
| doctrinal-adjunction → graded-monad | outbound | `scope:compose` | Graded monad arises from doctrinal adjunction |
| graded-monad → doctrinal-adjunction | inbound | `scope:change` | Index category adjunction needs doctrinal lift |
| doctrinal-adjunction → catsharp-galois | outbound | `scope:compose` | Galois adjunction α ⊣ γ is doctrinal |
| catsharp-galois → doctrinal-adjunction | inbound | `scope:change` | CatSharp bridge requires doctrinal coherence |
| doctrinal-adjunction → linear-logic | outbound | `scope:verify` | Linear negation swaps lax/colax |
| linear-logic → doctrinal-adjunction | inbound | `scope:verify` | Duality validates mate correspondence |

### Mutual Awareness Summary

```
      synthetic-adj (+1)
            ↑ change
            │
kan-ext (0) ←── DOCTRINAL-ADJ (0) ──→ 2-monad (0)
            │           │
            ↓ compose   ↓ change
    open-games (0)   bidirectional (0)

+ 6 additional edges to existing skills
```

**Total edges**: 20 (10 bidirectional pairs)
**Propagator balance**: 6 scope:change + 8 scope:compose + 6 scope:verify = balanced

## GF(3) Triads

```
codescent (-1) ⊗ doctrinal-adjunction (0) ⊗ flexible-algebra (+1) = 0 ✓  [BKP Lifting]
sheaf-cohomology (-1) ⊗ doctrinal-adjunction (0) ⊗ synthetic-adjunctions (+1) = 0 ✓  [Adjunction-Monad]
linear-logic (-1) ⊗ doctrinal-adjunction (0) ⊗ free-monad-gen (+1) = 0 ✓  [Resource-Adjunction]
segal-types (-1) ⊗ doctrinal-adjunction (0) ⊗ operad-compose (+1) = 0 ✓  [Operadic-Lifting]
covariant-fibrations (-1) ⊗ doctrinal-adjunction (0) ⊗ discopy-operads (+1) = 0 ✓  [Fibered-Lifting]
```

## Commands

```bash
just doctrinal-lift f u T          # Lift adjunction f ⊣ u through T
just doctrinal-mate lax-cell       # Compute mate of lax cell → colax cell
just doctrinal-verify adj T        # Verify doctrinal adjunction conditions
just doctrinal-examples T          # List known doctrinal adjunctions for T
```

## References

- Kelly, G.M. (1974). "Doctrinal adjunction." *LNM* 420:257-280
- Blackwell, Kelly & Power (1989). "Two-dimensional monad theory." *JPAA* 59:1-41
- Lack, S. (2010). "A 2-categories companion." *IMA Vol. Math. Appl.* 152:105-191
- Kelly, G.M. & Street, R. (1974). "Review of the elements of 2-categories." *LNM* 420:75-103

## SDF Interleaving

### Primary Chapter: 5. Evaluation

**Concepts**: eval, apply, interpreter, environment

### GF(3) Balanced Triad

```
doctrinal-adjunction (0) + SDF.Ch5 (0) + [balancer] (0) = 0
```

**Skill Trit**: 0 (ERGODIC - coordination)

### Connection Pattern

Evaluation interprets expressions. Doctrinal adjunction interprets T-algebra structure through the mate correspondence, transporting between lax (evaluation) and colax (co-evaluation) modes.


## CT lattice atlas

Part of: `para-mensch-commons` (CT lattice family).
