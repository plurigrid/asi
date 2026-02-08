---
name: epistemic-arbitrage
description: Propagator-based parallel structure for exploiting knowledge differentials
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Epistemic Arbitrage: Propagator-Based Knowledge Synthesis

Epistemic arbitrage exploits **knowledge differentials** between domains. When concept A in domain X is well-understood, but its isomorphic counterpart A' in domain Y is mysterious, we can **arbitrage** by transferring understanding.

## Core Architecture

### Propagator Networks (Radul/Sussman)

A propagator network consists of:

```
┌─────────┐     ┌─────────────┐     ┌─────────┐
│  Cell A │────▶│ Propagator  │────▶│  Cell B │
│ (known) │     │  (transfer) │     │(derived)│
└─────────┘     └─────────────┘     └─────────┘
```

- **Cells**: Containers for partial information
- **Propagators**: Functions that combine/transform information
- **Merging**: Monotonic accumulation (information only increases)

### SplitMixTernary RNG

For parallel propagation with determinism:

```ruby
class SplitMixTernary
  GOLDEN = 0x9e3779b97f4a7c15  # Golden ratio constant
  
  def initialize(seed)
    @state = seed
  end
  
  def next_ternary
    # Advance state (SplitMix64)
    @state = (@state + GOLDEN) & 0xFFFFFFFFFFFFFFFF
    z = @state
    z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & 0xFFFFFFFFFFFFFFFF
    z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & 0xFFFFFFFFFFFFFFFF
    z = z ^ (z >> 31)
    
    # Map to ternary: -1, 0, +1
    (z % 3) - 1
  end
  
  def split(index)
    # Create independent child stream
    child_seed = @state ^ (index * GOLDEN)
    SplitMixTernary.new(child_seed)
  end
end
```

## Arbitrage Patterns

### Pattern 1: Domain Transfer

```ruby
# Knowledge in domain A
cell_a = Cell.new(:music, :circle_of_fifths)
cell_a.add_info(:structure, :cyclic_group_12)
cell_a.add_info(:generator, :perfect_fifth)

# Unknown in domain B
cell_b = Cell.new(:number_theory, :modular_arithmetic)

# Propagator transfers structure
propagator = Propagator.new(:domain_transfer) do |source, target|
  if source.has?(:structure)
    target.merge(:structure, source.get(:structure))
    target.merge(:insight, "Z/12Z isomorphic t