---
name: temporal-coalgebra
description: Coalgebraic observation of derivation streams with final coalgebra bisimulation
  for infinite trace verification.
license: UNLICENSED
metadata:
  source: local
---

# Temporal Coalgebra Skill: Observation Duality

**Status**: ✅ Production Ready
**Trit**: -1 (MINUS - validator/observer)
**Color**: #2626D8 (Blue)
**Principle**: Observe behaviors → Verify equivalence
**Frame**: Final coalgebra with stream coalgebra traces

---

## Overview

**Temporal Coalgebra** is the dual of algebra: where algebra constructs, coalgebra observes. Implements:

1. **Observation functor**: O: Derivation → Observation
2. **Final coalgebra**: νF for maximal bisimulation
3. **Stream coalgebra**: Infinite traces with head/tail
4. **three-match integration**: Game verification via bisimulation

**Correct by construction**: Two systems are equivalent iff they are bisimilar (observationally indistinguishable).

## Core Formula

```
Coalgebra: (X, γ: X → F(X))   # State → Observable structure
Final:     νF = lim F^n(1)     # Greatest fixpoint

Bisimulation R ⊆ X × Y:
  (x, y) ∈ R ⟹ F(R)(γ_X(x), γ_Y(y))
```

For derivation observation:
```ruby
# Observe derivation stream
observe(derivation) = { head: current_step, tail: rest_of_derivation }

# Two derivations are equivalent iff:
bisimilar?(d1, d2) == (observe(d1).head == observe(d2).head &&
                       bisimilar?(observe(d1).tail, observe(d2).tail))
```

## Why Coalgebra for Verification?

1. **Behavioral equivalence**: Same observations = same system
2. **Infinite structures**: Streams, trees, processes
3. **Game semantics**: Attacker/defender games are coalgebraic
4. **Lazy evaluation**: Observe only what's needed

## Gadgets

### 1. ObservationFunctor

Transform derivations into observations:

```ruby
functor = TemporalCoalgebra::ObservationFunctor.new(
  source: :derivation_chain,
  target: :observation_stream
)
observation = functor.apply(derivation)
observation.head      # => current observable state
observation.tail      # => remaining stream (lazy)
observation.finite?   # => false (potentially infinite)
```

### 2. FinalCoalgebra

Construct the final coalgebra for type F:

```ruby
final = TemporalCoalgebra::FinalCoalgebra.new(
  functor: stream_functor,
  approximation_depth: 100
)
final.carrier           # => νF (greatest fixpoint)
final.universal?(coal)  # => check if coal maps uniquely
final.unfold(seed)      # => generate infinite structure
```

### 3. BisimulationChecker

Verify behavioral equivalence:

```ruby
checker = TemporalCoalgebra::BisimulationChecker.new
checker.add_system(:system_a, coalgebra_a)
checker.add_system(:system_b, coalgebra_b)

result = checker.check_bisimilar!
result[:bisimilar]         # => true/false
result[:distinguishing_trace]  # => if false, witness
result[:depth_checked]     # => how deep we verified
```

### 4. StreamCoalgebra

Work with infinite streams:

```ruby
stream = TemporalCoalgebra::StreamCoalgebra.new(seed: 0x42D)
stream.head              # => first element
stream.tail              # => rest of stream
stream.take(10)          # => first 10 elements
stream.drop(5).head      # => 6th element
stream.map { |x| x * 2 } # => transformed stream
stream.zip(other_stream) # => paired stream
```

### 5. ThreeMatchBisimulation

Integration with three-match for game verification:

```ruby
game = TemporalCoalgebra::ThreeMatchBisimulation.new(
  attacker: player_a,
  defender: player_b,
  three_match_gadget: gadget
)
game.play_round!
game.defender_wins?      # => strategies are bisimilar
game.attacker_wins?      # => found distinguishing move
game.gf3_conserved?      # => trit sum = 0
```

## Commands

```bash
# Observe derivation chain
just coalgebra-observe

# Check bisimulation
just coalgebra-bisim system_a system_b

# Generate stream from seed
just coalgebra-stream 0x42D 20

# Verify game equivalence
just coalgebra-game
```

## API

```ruby
require 'temporal_coalgebra'

# Create observation system
obs = TemporalCoalgebra::Observer.new(
  trit: -1,
  functor: :stream
)

# Observe derivation
stream = obs.observe(derivation_chain)

# Check equivalence
bisim = obs.bisimilar?(stream_a, stream_b)

# Integrate with three-match
game_result = obs.verify_game(three_match_gadget)
```

## Integration with GF(3) Triads

Forms valid triads with ERGODIC (0) and PLUS (+1) skills:

```
temporal-coalgebra (-1) ⊗ unworld (0) ⊗ gay-mcp (+1) = 0 ✓
temporal-coalgebra (-1) ⊗ glass-bead-game (0) ⊗ cider-clojure (+1) = 0 ✓
temporal-coalgebra (-1) ⊗ acsets (0) ⊗ rubato-composer (+1) = 0 ✓
```

## Mathematical Foundation

### Coalgebra Definition

```
Coalgebra for F: (X, γ: X → F(X))
  - X is carrier (state space)
  - γ is structure map (observation)
  - F is endofunctor (observation type)
```

### Stream Functor

```
F(X) = A × X    (head × tail)
νF ≅ A^ω       (infinite sequences)
```

### Bisimulation

```
R is bisimulation ⟺
  ∀(x,y) ∈ R: (γ_X(x), γ_Y(y)) ∈ F(R)

Behavioral equivalence: x ∼ y ⟺ ∃R bisimulation. (x,y) ∈ R
```

### Coinduction Principle

```
To prove P(ν F), show:
  P is F-consistent: P(x) ⟹ P(tail(x))
  P(seed) holds
```

## Example Output

```
─── Temporal Coalgebra Observation ───
Source: Derivation chain (length ∞)
Functor: Stream (head × tail)

Observation:
  head: { seed: 0x42D, color: #2626D8, trit: -1 }
  tail: <lazy stream>

Bisimulation Check:
  System A: derivation_chain_1
  System B: derivation_chain_2
  
  Depth 0: heads match ✓
  Depth 1: tails match ✓
  Depth 2: tails match ✓
  ...
  Depth 100: tails match ✓

Result: BISIMILAR (observationally equivalent)
GF(3) Trit: -1 (MINUS/Observer)

─── Three-Match Integration ───
Game: Attacker vs Defender
Rounds: 12
Winner: Defender (strategies bisimilar)
GF(3) conserved: true
```

---

**Skill Name**: temporal-coalgebra
**Type**: Observation / Bisimulation Verification
**Trit**: -1 (MINUS)
**Color**: #2626D8 (Blue)
**GF(3)**: Forms valid triads with ERGODIC + PLUS skills
**Dual**: Algebra (construction) ↔ Coalgebra (observation)
