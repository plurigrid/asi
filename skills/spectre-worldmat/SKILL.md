---
name: spectre-worldmat
description: "Spectre monotile principles applied to Worldmat thread evolution with GF(3) conservation"
trit: 0
---

# spectre-worldmat

Synthesis of **aperiodic monotile geometry** and **Worldmat TiDAR execution**.

## Core Insight

The Spectre monotile achieves global aperiodicity through local edge-matching rules. Similarly, threads evolve aperiodically through local GF(3) conservation constraints.

## Metatile → Thread Archetype Mapping

| Metatile | Thread Type | GF(3) | Pattern |
|----------|-------------|-------|---------|
| Γ Gamma | SEED | 0 | Bifurcating origin (2 spectres) |
| Δ Delta | BRIDGE | +1 | 8-way cross-domain synthesis |
| Θ Theta | RECURSIVE | -1 | Self-referential loops |
| Λ Lambda | ABSTRACTION | 0 | Meta-level generalization |
| Ξ Xi | INTEGRATION | +1 | Unification of disparate concepts |
| Π Pi | EXPANSION | -1 | Proliferation and scaling |
| Σ Sigma | AGGREGATION | 0 | Spur-edge decentralized collection |
| Φ Phi | GENERATOR | +1 | Ubiquitous production (in all subs) |
| Ψ Psi | TERMINAL | -1 | Boundary interface |

## Mod12 = GF(3) × Z/4Z

12 rotations decompose into 3 trits × 4 temporal phases:

```
Dawn  (phase 0): ergodic(0), plus(1), minus(2)
Noon  (phase 1): ergodic(3), plus(4), minus(5)
Dusk  (phase 2): ergodic(6), plus(7), minus(8)
Night (phase 3): ergodic(9), plus(10), minus(11)
```

## Conservation Laws

1. **Γ-Σ Conservation**: Every substitution contains exactly 1 Gamma and 1 Sigma
2. **Φ Abundance**: Generator appears 2+ times in every expansion
3. **GF(3) Balance**: Sum of trits across any substitution ≡ 0 (mod 3)

## TrigNum 4D Embedding

```haskell
data TrigNum a = TrigNum a a a a
-- Spans hexagonal lattice: {1, √3/2+i/2, 1/2+i√3/2, i}
-- Parity constraint: parity(a,d) = parity(b,c)
```

Threads embed in 4D space with coherence verified by parity matching.

## Worldmat Integration

```python
from worldmat import Worldmat

wm = Worldmat(master_seed=0x87079c9f1d3b0474)
wm.execute_parallel()

# 27 cells = 3³ = 9 metatile types × 3 instances
# Each cell is a TiDAR execution (diffusion + AR verify)
# GF(3) conserved across all 9 slices
```

## Skill Growth Pattern

Skills grow via golden angle (137.5°) knight tour:

```
Position 1  → #DD3C3C (scarlet)  @ hue 0°
Position 2  → #3CDD6B (mint)     @ hue 137.5°
Position 3  → #9A3CDD (violet)   @ hue 275°
...
Position 27 → #DD3C7E (rose)     @ hue 335.2°
```

After 27 positions, full coverage. Never repeats (aperiodic).

## Usage

```bash
# Run worldmat demo
python3 /Users/bob/ies/worldmat/worldmat.py

# Verify SPI
python3 /Users/bob/ies/worldmat/worldmat.py verify

# Grow skill at next position
python3 /Users/bob/ies/worldmat/skill_grower.py grow "context"

# Check tour status
python3 /Users/bob/ies/worldmat/skill_grower.py status
```

## Related Files

- [worldmat.py](file:///Users/bob/ies/worldmat/worldmat.py) - Core implementation
- [skill_grower.py](file:///Users/bob/ies/worldmat/skill_grower.py) - Gay MCP integration
- [Spectre.hs](file:///Users/bob/ies/aperiodic/src/Tilings/Spectre.hs) - Haskell monotile
- [plus_monotile_predictions.json](file:///Users/bob/ies/worldmat/plus_monotile_predictions.json) - PLUS agent

## GF(3) Triad

```
MINUS (-1): minus_verification_sink.json  - stale thread analysis
ERGODIC(0): ergodic_thread_state.json     - current network state
PLUS  (+1): plus_monotile_predictions.json - future predictions
```

Sum: -1 + 0 + 1 = 0 ✓
