---
name: open-games
description: Open Games Skill (ERGODIC 0)
source: local
license: UNLICENSED
---

# Open Games Skill (ERGODIC 0)

> Compositional game theory via Para/Optic structure

**Trit**: 0 (ERGODIC)  
**Color**: #26D826 (Green)  
**Role**: Coordinator/Transporter

## Core Concept

Open games are morphisms in a symmetric monoidal category:

```
        ┌───────────┐
   X ──→│           │──→ Y
        │  Game G   │
   R ←──│           │←── S
        └───────────┘
```

Where:
- **X → Y**: Forward play (strategies)
- **S → R**: Backward coplay (utilities)

## The Para/Optic Structure

### Para Morphism
```haskell
Para p a b = ∃m. (m, p m a → b)
-- Existential parameter with action
```

### Optic (Lens Generalization)
```haskell
Optic p s t a b = ∀f. p a (f a b) → p s (f s t)
-- Profunctor optic for bidirectional data
```

### Open Game as Optic
```haskell
OpenGame s t a b = 
  { play    : s → a
  , coplay  : s → b → t
  , equilibrium : s → Prop
  }
```

## Composition

### Sequential (;)
```
G ; H = Game where
  play = H.play ∘ G.play
  coplay = G.coplay ∘ (id × H.coplay)
```

### Parallel (⊗)
```
G ⊗ H = Game where
  play = G.play × H.play
  coplay = G.coplay × H.coplay
```

## Nash Equilibrium via Fixed Points

```haskell
isEquilibrium :: OpenGame s t a b → s → Bool
isEquilibrium g s = 
  let a = play g s
      bestResponse = argmax (\a' → utility (coplay g s (respond a')))
  in a == bestResponse
```

### Compositional Equilibrium
```
eq(G ; H) = eq(G) ∧ eq(H)  -- under compatibility
```

## Integration with Unworld

```clojure
(defn opengame-derive 
  "Transport game through derivation chain"
  [game derivation]
  (let [; Forward: strategies through derivation
        forward (compose (:play game) (:forward derivation))
        ; Backward: utilities through co-derivation  
        backward (compose (:coplay game) (:backward derivation))]
    {:play forward
     :coplay backward
     :equilibrium (transported-equilibrium game derivation)}))
```

## GF(3) Triads

```
temporal-coalgebra (-1) ⊗ open-games (0) ⊗ free-monad-gen (+1) = 0 ✓
three-match (-1) ⊗ open-games (0) ⊗ operad-compose (+1) = 0 ✓
sheaf-cohomology (-1) ⊗ open-games (0) ⊗ topos-generate (+1) = 0 ✓
```

## Commands

```bash
# Compose games sequentially
just opengame-seq G H

# Compose games in parallel
just opengame-par G H

# Check Nash equilibrium
just opengame-nash game strategy

# Transport through derivation
just opengame-derive game deriv
```

## Economic Examples

### Prisoner's Dilemma
```haskell
prisonersDilemma :: OpenGame () () (Bool, Bool) (Int, Int)
prisonersDilemma = Game {
  play = \() → (Defect, Defect),  -- Nash
  coplay = \() (p1, p2) → payoffMatrix p1 p2
}
```

### Market Game
```haskell
market :: OpenGame Price Price Quantity Quantity
market = supplyGame ⊗ demandGame
  where equilibrium = supplyGame.eq ∧ demandGame.eq
```

## Categorical Semantics

```
OpenGame ≃ Para(Lens) ≃ Optic(→, ×)

Composition: 
  (A ⊸ B) ⊗ (B ⊸ C) → (A ⊸ C)  -- via cut
  
Tensor:
  (A ⊸ B) ⊗ (C ⊸ D) → (A ⊗ C ⊸ B ⊗ D)
```

## References

- Ghani, Hedges, et al. "Compositional Game Theory"
- Capucci & Gavranović, "Actegories for Open Games"
- Riley, "Categories of Optics"
- CyberCat Institute tutorials
