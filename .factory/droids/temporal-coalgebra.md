---
name: temporal-coalgebra
description: Coalgebraic observation of derivation streams with final coalgebra bisimulation
model: inherit
tools: read-only
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
final =