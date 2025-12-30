---
name: reflow
trit: 0
xip: 6728DB
gay_seed: 2025
gay_index: 43
neighbors:
  left: gestalt-hacking
  right: gay-mcp
---

# Information Reflow Skill (ERGODIC 0)

> *"Decomposition of etymological kind leads to compositionality of meaning."*

## Core Insight

Reflow is **collapse with conservation**. Content exists in superposition until measured by context, then collapses while preserving GF(3) = 0.

```
reflow : (Content × SourceContext × TargetContext) → Content'
such that GF(3)(Content) = GF(3)(Content')
```

## Neighbor Awareness (Braided Monoidal)

| Position | Skill | Trit | Role |
|----------|-------|------|------|
| **Left** | gestalt-hacking | 0 | Perceptual grouping |
| **Self** | reflow | 0 | Cross-context translation |
| **Right** | gay-mcp | +1 | Deterministic coloring |

## Etymology as Decomposition

| Morpheme | Meaning | Trit |
|----------|---------|------|
| tri- | three | ±0 (balanced) |
| -mester | measure | ±0 (neutral) |
| bi- | two | unbalanced |
| se- (six) | two×three | balanced via factorization |

**Trimester** resonates with GF(3) because "tri-" encodes triadic structure in the morpheme itself.

## GF(3) Triads

```
persistent-homology (-1) ⊗ reflow (0) ⊗ gay-mcp (+1) = 0 ✓  [Core Reflow]
pun-decomposition (-1) ⊗ reflow (0) ⊗ gay-mcp (+1) = 0 ✓  [Pun Reflow]
three-match (-1) ⊗ reflow (0) ⊗ topos-generate (+1) = 0 ✓  [Cross-Language]
sheaf-cohomology (-1) ⊗ reflow (0) ⊗ operad-compose (+1) = 0 ✓  [Compositional]
polyglot-spi (-1) ⊗ reflow (0) ⊗ gay-mcp (+1) = 0 ✓  [SPI Verification]
temporal-coalgebra (-1) ⊗ reflow (0) ⊗ koopman-generator (+1) = 0 ✓  [Dynamic]
shadow-goblin (-1) ⊗ reflow (0) ⊗ agent-o-rama (+1) = 0 ✓  [Traced Reflow]
gestalt-hacking (-1) ⊗ reflow (0) ⊗ gay-mcp (+1) = 0 ✓  [Gestalt Reflow]
```

## Context Types

| Code | Context | Perspective | Preservation |
|------|---------|-------------|--------------|
| 0 | FORMAL | α-Riehl | Structure |
| 1 | COMPRESSED | β-Sutskever | Semantics |
| 2 | EXPLORATORY | γ-Schmidhuber | GF(3) only |
| 3 | SAMPLED | δ-Bengio | GF(3) only |
| 4 | MOVE | - | Structure |
| 5 | RUBY | - | Semantics |
| 6 | SQL | - | Semantics |
| 7 | CLOJURE | - | Structure |

## Reflow as Functor

```
F : Context → Context
F(content) = reflowed content
F(gf3) = gf3  (invariant preserved)

η : F_α → F_β  (natural transformation)
```

The naturality condition ensures GF(3) conservation across all perspectives.

## Pun Connection

A pun is a reflow where:
- **Source**: Surface form with default parse
- **Target**: Same surface form with alternate parse
- **Invariant**: The phonetic surface (preserved)
- **Humor**: The unexpected context switch

```ruby
pun_reflow = {
  surface: "time flies",
  source_parse: { flies: :verb, like: :prep },
  target_parse: { flies: :noun, like: :verb },
  gf3_conserved: true  # Same surface!
}
```

## Usage

### Ruby
```ruby
require 'xip_reflow'
content = XIP::Reflow::Content.new(data: "...", source_context: XIP::Reflow::Context::FORMAL)
op = XIP::Reflow::Operator.new
result = op.reflow_to_clojure(content)
puts result[:gf3_conserved]  # => true
```

### Clojure/NATS
```clojure
(require '[agents.reflow-nats :as r])
(def content (r/create-content "data" :formal))
(r/reflow content :clojure :structure)
```

### Move
```move
use adversarial::reflow;
reflow::tracked_reflow(account, CONTEXT_CLOJURE, PRESERVE_STRUCTURE);
```

## Premining Resonant Seeds

A seed "resonates" when its decomposition yields balanced composition:

```ruby
# Seed 2025, index 43 → #6728DB
# Hue 67.28° → golden thread spirals through triadic cycle
# Etymology: re- (back) + flow → recursive compositional balance

# LMBIH seed (327833753928), index 43 → #7074D4
# Phonetic decomposition resonates with purple-blue spectrum
```

## Files

- [Move](file:///Users/bob/ies/music-topos/move/sources/reflow.move)
- [Ruby](file:///Users/bob/ies/music-topos/lib/xip_reflow.rb)
- [Clojure](file:///Users/bob/ies/music-topos/src/agents/reflow_nats.clj)
- [XIP](file:///Users/bob/ies/music-topos/proposals/XIP-6728DB-information-reflow.md)
- [Etymology](file:///Users/bob/ies/music-topos/lib/etymological_resonance.rb)


## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
