---
name: glass-bead-game
description: Hesse-inspired interdisciplinary synthesis game with Badiou triangle
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Glass Bead Game: Topos of Music

The Glass Bead Game (Glasperlenspiel) is an interdisciplinary synthesis engine that connects:
- **Mathematics** (category theory, algebraic geometry, number theory)
- **Music** (harmony, counterpoint, electronic synthesis)
- **Philosophy** (Badiou's ontology, Girard's linear logic, Lawvere's topos theory)

## Core Concept: World Hopping

Each **bead** represents a concept in a specific domain. Beads connect via **morphisms** that preserve essential structure. The game consists of finding paths between distant beads that illuminate hidden connections.

### Badiou Triangle Inequality

For any three worlds W₁, W₂, W₃:

```
d(W₁, W₃) ≤ d(W₁, W₂) + d(W₂, W₃)
```

This is the **triangle inequality** that governs world hopping:

- **Being**: Current ontological state (the bead's position in possibility space)
- **Event**: A rupture that creates new possibilities (the hop between worlds)  
- **Truth**: What persists across the transition (the invariant structure)

### Distance Metric

Distance between worlds is measured by:

```ruby
def world_distance(w1, w2)
  being_diff = (w1.seed ^ w2.seed).to_s(2).count('1')  # Hamming distance
  event_diff = (w1.epoch - w2.epoch).abs               # Temporal distance
  truth_diff = conjugacy_distance(w1.invariant, w2.invariant)
  
  Math.sqrt(being_diff**2 + event_diff**2 + truth_diff**2)
end
```

## Bead Types

### Mathematical Beads
- **Number**: Prime, composite, transcendental, p-adic
- **Structure**: Group, ring, field, category, topos
- **Morphism**: Homomorphism, functor, natural transformation
- **Invariant**: Fixed point, eigenvalue, cohomology class

### Musical Beads  
- **Pitch**: Frequency, pitch class, interval
- **Harmony**: Chord, progression, voice leading
- **Rhythm**: Duration, meter, polyrhythm
- **Timbre**: Spectrum, envelope, modulation

### Philosophical Beads
- **Ontological**: Being, becoming, event, void
- **Logical**: Proposition, proof, cut, polarity
- **Categorical**: Obje