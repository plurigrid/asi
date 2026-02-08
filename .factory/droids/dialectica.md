---
name: dialectica
description: Dialectica Skill (ERGODIC 0)
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Dialectica Skill (ERGODIC 0)

> Proof-as-game interpretation via Gödel's Dialectica

**Trit**: 0 (ERGODIC)  
**Color**: #26D826 (Green)  
**Role**: Coordinator/Transporter

## Core Concept

Dialectica transforms proofs into games:

```
A ⊢ B  becomes  ∃x. ∀y. R(x, y)
```

Where:
- **x** = Proponent's move (witness/strategy)
- **y** = Opponent's challenge
- **R(x,y)** = Winning condition (atomic)

## The Dialectica Interpretation

### For Logical Connectives

```
D(A ∧ B) = ∃(x,x').∀(y,y'). D(A)[x,y] ∧ D(B)[x',y']

D(A → B) = ∃f,F. ∀x,y. D(A)[x, F(x,y)] → D(B)[f(x), y]

D(∀z.A) = ∃f. ∀z,y. D(A)[f(z), y]

D(∃z.A) = ∃(z,x). ∀y. D(A)[x, y]
```

### Key Insight: Functions as Strategies
- **f** extracts witnesses from proofs
- **F** back-propagates challenges
- Composition = strategy composition

## Integration with Glass Bead Game

```ruby
# World hop via Dialectica
def dialectica_hop(proposition, world_state)
  # Transform proposition to game
  game = {
    proponent_moves: extract_witnesses(proposition),
    opponent_moves: extract_challenges(proposition),
    winning: atomic_condition(proposition)
  }
  
  # Play generates new world
  new_world = play_game(game, world_state)
  
  # GF(3) conservation check
  verify_gf3(world_state, new_world)
end
```

## Attack/Defense Structure

```
        Proponent (∃)
            ↓ witness x
        Opponent (∀)
            ↓ challenge y
        Proponent
            ↓ response (via f, F)
           ...
        Atomic check R(x,y)
```

## Linear Logic Decomposition

Dialectica splits into multiplicative/additive:

```
A ⊸ B = (A⊥ ⅋ B)    # Linear implication
A ⊗ B               # Tensor (both needed)
A & B               # With (choice)
A ⊕ B               # Plus (given)
!A                  # Of course (reusable)
?A                  # Why not (garbage)
```

### Chu Construction
```
Chu(Set, ⊥) ≃ *-autonomous category
Objects: (A⁺, A⁻, ⟨-,-⟩: A⁺ × A⁻ → ⊥)
```

## GF(3) Triads

```
three-match (-1) ⊗ dialectica (0) ⊗ gay-mcp (+1) =