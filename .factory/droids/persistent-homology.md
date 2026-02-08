---
name: persistent-homology
description: Topological data analysis for stable feature verification across filtrations
model: inherit
tools: read-only
---

# Persistent Homology Skill: Stable Feature Verification

**Status**: ✅ Production Ready
**Trit**: -1 (MINUS - validator/analyzer)
**Color**: #2626D8 (Blue)
**Principle**: Stable features → Robust structure
**Frame**: Filtration with persistence diagrams

---

## Overview

**Persistent Homology** identifies topological features that persist across scales. Implements:

1. **Filtration**: Nested sequence of complexes by parameter
2. **Betti numbers**: β₀ (components), β₁ (holes), β₂ (voids)
3. **Persistence diagrams**: Birth-death pairs for features
4. **radare2 integration**: Binary analysis for structure holes

**Correct by construction**: Features with long persistence are stable/significant; short-lived features are noise.

## Core Formula

```
Filtration: K₀ ⊆ K₁ ⊆ ... ⊆ Kₙ  (by threshold ε)
Homology:   H_k(K_i) for each level
Persistence: (birth_i, death_j) for each feature

Stability Theorem:
  d_B(Dgm(f), Dgm(g)) ≤ ||f - g||_∞
```

For code complexity:
```ruby
# Filtration by cyclomatic complexity threshold
filtration = [
  threshold_0: simple_functions,
  threshold_5: moderate_functions,
  threshold_10: complex_functions,
  threshold_20: very_complex_functions
]

# Persistent features survive across thresholds
stable_structure = features.select { |f| f.persistence > 5 }
```

## Why Persistent Homology for Code?

1. **Complexity filtration**: Track structure across complexity levels
2. **Structural holes**: β₁ > 0 means cyclic dependencies
3. **Stability**: Long-lived features are fundamental
4. **Noise filtering**: Short-lived features are incidental

## Gadgets

### 1. ComplexityFiltration

Build filtration from code complexity:

```ruby
filtration = PersistentHomology::ComplexityFiltration.new(
  source: :codebase,
  metric: :cyclomatic_complexity
)
filtration.add_file("src/core.clj")
filtration.build!

filtration.levels           # => [0, 5, 10, 15, 20]
filtration.complex_at(10)   # => simplicial complex at threshold 10
filtration.inclusion(5, 10) # => inc