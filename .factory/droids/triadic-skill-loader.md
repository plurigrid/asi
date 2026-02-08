---
name: triadic-skill-loader
description: Triadic Skill Loader
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Triadic Skill Loader

> **Trit**: 0 (ERGODIC) - Coordinates balanced skill loading

**Principle**: Load 3 skills at a time, every interaction, with GF(3) conservation.

## Core Invariant

```
∀ interaction: load(skill₋₁) ⊗ load(skill₀) ⊗ load(skill₊₁) = 0 (mod 3)
```

## Skill Triad Catalog

### Structural Triads

| Minus (-1) | Ergodic (0) | Plus (+1) | Domain |
|------------|-------------|-----------|--------|
| structured-decomp | mutual-awareness-backlink | gh-interactome | Awareness |
| sheaf-cohomology | cognitive-superposition | gflownet | Intelligence |
| kolmogorov-compression | triad-interleave | curiosity-driven | Learning |
| segal-types | bumpus-narratives | world-hopping | Categories |
| persistent-homology | unworld | gay-mcp | Topology |

### Execution Triads

| Minus (-1) | Ergodic (0) | Plus (+1) | Domain |
|------------|-------------|-----------|--------|
| clj-kondo-3color | acsets-relational-thinking | rama-gay-clojure | Clojure |
| three-match | specter-acset | bisimulation-game | Navigation |
| sheaf-laplacian | interactome-rl-env | jaxlife-open-ended | RL |

## Loading Protocol

```python
class TriadicSkillLoader:
    """Load skills in balanced triads every interaction."""
    
    TRIADS = [
        # Cognitive triad
        ("sheaf-cohomology", "cognitive-superposition", "gflownet"),
        # Awareness triad  
        ("structured-decomp", "mutual-awareness-backlink", "gh-interactome"),
        # Interleaving triad
        ("kolmogorov-compression", "triad-interleave", "curiosity-driven"),
        # Category triad
        ("segal-types", "bumpus-narratives", "world-hopping"),
        # Game triad
        ("three-match", "bisimulation-game", "gay-mcp"),
    ]
    
    def __init__(self, seed: int = 0x42D):
        self.seed = seed
        self.rng = SplitMix64(seed)
        self.interaction_count = 0
        self.loaded_triads = []
    
    def next_triad(self) -> tuple:
        """Select next triad using golden angle rotation."""
       