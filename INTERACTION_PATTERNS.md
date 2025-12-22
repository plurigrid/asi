# Interaction Pattern Types via Ramanujan Walk + Pontryagin Duality

**Synthesis Date**: 2025-12-22
**Seed**: 0x42D | **GF(3) Status**: CONSERVED ✓

## Overview

This document defines **interaction pattern types** discovered through random walks on a Ramanujan complex, with types expressible as:
1. **Colors** (OkLCH via gay-mcp)
2. **Pontryagin dual characters** (frequency analysis on GF(3))
3. **GF(3) trit signatures** (constraint/balance/generation)

## Pattern Type Catalog

| Pattern | Trit | Color | Character | Description |
|---------|------|-------|-----------|-------------|
| **constraint_convergent** | ⊖ (-1) | `oklch(0.50 0.15 270)` | χ₀ | Validation converging to stable constraint satisfaction |
| **constraint_oscillating** | ⊖ (-1) | `oklch(0.55 0.18 290)` | χ₁ | Cyclic validation patterns (retry/backoff) |
| **coordination_stable** | ○ (0) | `oklch(0.60 0.12 180)` | χ₀ | Stable coordination achieving global coherence |
| **coordination_adaptive** | ○ (0) | `oklch(0.65 0.14 200)` | χ₂ | Adaptive coordination with responsive switching |
| **generation_exploratory** | ⊕ (+1) | `oklch(0.65 0.20 30)` | χ₂ | High-entropy generative exploration |
| **generation_surprising** | ⊕ (+1) | `oklch(0.70 0.25 60)` | χ₀ | Low-probability, high-value emergent patterns |
| **tripartite_balanced** | ○ (0) | `oklch(0.72 0.22 120)` | χ₀ | Perfect GF(3) conservation: MINUS + ZERO + PLUS = 0 |

## Pontryagin Dual Characters

The Pontryagin dual of GF(3) is GF(3) itself. Characters χₖ reveal frequency structure:

```
χ₀(t) = 1           (trivial - uniform distribution)
χ₁(t) = ω^t         (cyclic rotation - forward bias)
χ₂(t) = ω^(2t)      (anti-cyclic - backward bias)

where ω = e^(2πi/3)
```

**Spectral Analysis** (from session):
- χ₀ weight: **0.556** → Dominant (rapid mixing achieved)
- χ₁ weight: **0.222** → Moderate cyclic structure
- χ₂ weight: **0.222** → Moderate anti-cyclic

**Interpretation**: Trivial character dominance indicates the system rapidly mixes to uniform distribution—a signature of expander graph properties.

## Ramanujan Complex Structure

The interaction graph approximates a Ramanujan graph:

- **Vertices**: Skills, agents, interaction states
- **Edges**: Invocations, data flows, dependencies
- **Spectral gap**: 0.80 (target: 2√(k-1) ≈ 3.46 for k=4)
- **Non-backtracking walks**: Hashimoto matrix formulation

### Walk Categories

1. **Convergent** (low entropy, <1.5 bits)
   - Walks stabilizing in small vertex clusters
   - Energy interpretation: Low-energy attractor basins

2. **Oscillating** (medium entropy, 0.5-2.0 bits)
   - Periodic returns to visited vertices
   - Energy interpretation: Limit cycle behavior

3. **Exploratory** (high entropy, 2.5-5.0 bits)
   - Diffusive exploration covering many vertices
   - Energy interpretation: Brownian mixing regime

4. **Surprising** (GF(3) = 0, entropy 1.0-2.5 bits)
   - Low probability paths with conservation
   - Energy interpretation: Rare fluctuation → emergent structure

## GF(3) Conservation

Tripartite agent outputs sum to 0 mod 3:

```
MINUS (-1) + ERGODIC (0) + PLUS (+1) = 0 ✓
```

This conservation law ensures:
- No net "charge" in the system
- Balanced constraint/coordination/generation
- Self-correcting dynamics

## Color Semantics

### Trit → Hue Mapping

| Trit | Hue Range | Semantic |
|------|-----------|----------|
| ⊖ (-1) | 270-300° | Purple: Cool, constraint, verification |
| ○ (0) | 180-210° | Cyan: Balanced, coordination, ergodic |
| ⊕ (+1) | 30-60° | Orange: Warm, generation, exploration |

### Conservation in Color Space

A GF(3)-conserved triad forms a **triadic color harmony**:
- Purple (270°) + Cyan (180°) + Orange (30°) = balanced visual system
- This is NOT coincidental—it reflects the mathematical structure

## Files Generated

| Agent | File | Purpose |
|-------|------|---------|
| MINUS | [validate_skills.py](lib/validate_skills.py) | CI validator with GF(3) annotations |
| MINUS | [edge_phase_propagator.py](lib/edge_phase_propagator.py) | Sheaf-condition overlap manager |
| ERGODIC | [gh_acset_export.py](lib/gh_acset_export.py) | GitHub activity → ACSet JSON |
| ERGODIC | [coherence_periods.py](lib/coherence_periods.py) | Temporal cycle detection |
| PLUS | [ramanujan_walk.py](lib/ramanujan_walk.py) | Non-backtracking random walk |
| PLUS | [pattern_types.py](lib/pattern_types.py) | Pattern type definitions |
| SYNTHESIS | [pontryagin_synthesis.py](lib/pontryagin_synthesis.py) | Agent output unification |

## Usage

```python
from lib.pontryagin_synthesis import (
    PATTERN_TYPE_CATALOG,
    synthesize_agents,
    create_agent_outputs_from_session
)

# Get pattern types
for name, ptype in PATTERN_TYPE_CATALOG.items():
    print(f"{ptype.trit.name}: {name} → {ptype.to_css()}")

# Run synthesis
minus, ergodic, plus = create_agent_outputs_from_session()
synthesis = synthesize_agents(minus, ergodic, plus)
print(f"GF(3) conserved: {synthesis['synthesis']['gf3_conserved']}")
```

## See Also

- [gay-mcp skill](skills/gay-mcp/SKILL.md) - Deterministic color generation
- [acsets skill](skills/acsets/SKILL.md) - Algebraic databases
- [INTEGRATION_GUIDE.md](INTEGRATION_GUIDE.md) - Full Phase 3 skill ecosystem
