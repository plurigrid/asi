---
name: world-hopping
description: Badiou-inspired possible world navigation using triangle inequality constraints,
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# World Hopping: Possible World Navigation

World hopping is the art of navigating between **possible worlds** in mathematical/musical/philosophical space. Based on Badiou's ontology and Kripke semantics, with triangle inequality as the fundamental constraint.

## Possible Worlds

A **possible world** W is a configuration of:

```ruby
class PossibleWorld
  attr_reader :seed, :epoch, :state, :invariants, :accessibility
  
  def initialize(seed:, epoch: 0)
    @seed = seed                    # Ontological identity
    @epoch = epoch                  # Temporal position
    @state = compute_state          # Current configuration
    @invariants = []                # What persists across transitions
    @accessibility = {}             # Which worlds are reachable
  end
  
  def compute_state
    rng = SplitMixTernary.new(@seed + @epoch)
    {
      color: SeedMiner.color_at(@seed, @epoch),
      mathematician: select_mathematician(rng),
      operation: select_operation(rng),
      polarity: [:positive, :negative, :neutral][rng.next_ternary + 1]
    }
  end
end
```

## Accessibility Relations

### Modal Logic Foundation

- **Reflexive**: Every world can reach itself (∀W: W → W)
- **Symmetric**: If W₁ → W₂ then W₂ → W₁ (reversible hops)
- **Transitive**: If W₁ → W₂ → W₃ then W₁ → W₃ (composable paths)

### Accessibility Matrix

```ruby
class AccessibilityRelation
  def initialize(worlds)
    @matrix = {}
    worlds.each do |w1|
      @matrix[w1.seed] = {}
      worlds.each do |w2|
        @matrix[w1.seed][w2.seed] = accessible?(w1, w2)
      end
    end
  end
  
  def accessible?(w1, w2)
    distance = world_distance(w1, w2)
    max_hop = w1.state[:polarity] == :positive ? 3.0 : 2.0
    distance <= max_hop
  end
end
```

## Badiou's Event Ontology

### Being (L'être)

The **void** (∅) underlies all structure. Each world has a void-trace:

```ruby
def void_trace(world)
  # The minimal element that anchors the world
  world.invariants.min_by(&:complexity) || Void.new
end
`