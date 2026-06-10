---
name: open-games-plurigrid
description: 'This skill unifies:'
---
# Open Games Plurigrid Skill

> World-to-world interactions via compositional game theory with GF(3) energy consistency

**Trit**: 0 (ERGODIC)  
**Color**: `#26D826` (Green)  
**Synergy**: 0.59 (plurigrid ↔ jules-hedges)

## Overview

This skill unifies:
- **open-games**: Play/CoPlay bidirectional optics
- **ramanujan-expander**: Spectral gap λ₂ ≤ 2√(d-1)
- **glass-bead-game**: Triangle inequality d(W₁,W₃) ≤ d(W₁,W₂) + d(W₂,W₃)

## Core Insight

Play-Co-Play interactions are **energy-consistent open games**:

```
        ┌───────────────┐
   X ──→│               │──→ Y
        │  δ-Key Update │
   R ←──│               │←── S
        └───────────────┘

  Play (+1):   forward pass, propose action, derive delta
  CoPlay (-1): backward pass, adjust world, verify proof
  Bridge (0):  equilibrium, combine deltas, coordinate
  
  GF(3): (+1) + (-1) + (0) = 0 ✓ (energy conserved)
```

## Discovered Ecosystem

### Core Contributors (Git Log)

| Name | Contributions | Trit | Role |
|------|---------------|------|------|
| philipp-zahn | 216 | +1 | Maintainer |
| andrevidela | 76 | 0 | Contributor |
| jules-hedges | 40 | -1 | Founder |
| dxo | 15 | 0 | hevm integration |

### Repositories

| Repo | Stars | Description |
|------|-------|-------------|
| CyberCat-Institute/open-game-engine | 183 | Main implementation |
| jules-hedges/open-games | 13 | Original Haskell |
| plurigrid/open-games-hs | 0 | Plurigrid fork |
| LISA-ITMO/CGT4NN | 5 | Neural network games |

### Key Bridge Person

**clayrat (Alex Gryzlov)** @ IMDEA Software
- Stars BOTH open-games AND Catlab.jl
- Repos: dialectica, coherence-spaces, comonads
- The cobordism between compositional game theory ↔ applied category theory

**bgavran (Bruno Gavranović)** - Categorical Deep Learning
- 1459 stars on Category_Theory_Machine_Learning list
- Lens_Resources (56 stars) - optics theory
- Compositional_Deep_Learning (151 stars)

## World Hopping

### Distance Metric

```python
def world_distance(w1, w2, dr):
    # Hamming distance on fingerprints (being)
    being_diff = bin(fp1 ^ fp2).count('1') / 64.0
    # Epoch difference (temporal)
    epoch_diff = abs(w1.epoch - w2.epoch) / 100.0
    # Domain crossing
    domain_diff = 0.0 if w1.domain == w2.domain else 0.3
    
    return sqrt(being_diff² + epoch_diff² + domain_diff²)
```

### Triangle Inequality

For any hop W₁ → W₃ via W₂:
```
d(W₁, W₃) ≤ d(W₁, W₂) + d(W₂, W₃)
```

Elegance = direct_distance / path_distance (higher = better)

## Spectral Analysis

### Ramanujan Bound

For d-regular expander graph:
```
λ₂ ≤ 2√(d-1)
```

Observed: λ₁ = 0.053 after growing, bound = 2.14

### Growing the Expander

Add edges that maximize spectral gap:
1. Prefer cross-cluster connections
2. Maintain GF(3) balance
3. Respect domain boundaries

## Files

- `open_games_expander.py` - Graph discovery
- `play_coplay_protocol.py` - Delta update protocol
- `plurigrid_world_hop.py` - World hopping engine
- `delta_key_update.py` - Original delta protocol
- `gay_loot.py` - Synergy-based loot tables

## GF(3) Triads

```
temporal-coalgebra (-1) ⊗ open-games (0) ⊗ free-monad-gen (+1) = 0 ✓
sheaf-cohomology (-1) ⊗ open-games (0) ⊗ topos-generate (+1) = 0 ✓
ramanujan-expander (-1) ⊗ glass-bead-game (0) ⊗ world-hopping (+1) = 0 ✓
```

## Commands

```bash
# Run world hopping
python3 plurigrid_world_hop.py

# Play-CoPlay protocol
python3 play_coplay_protocol.py

# Expander graph discovery
python3 open_games_expander.py

# Delta key update demo
python3 delta_key_update.py
```

## Related Skills

- `open-games` - Core game theory
- `ramanujan-expander` - Spectral bounds
- `glass-bead-game` - World hopping
- `delta-key-update` - Key rotation protocol
- `gay-mcp` - Color fingerprints
- `bisimulation-game` - Observational equivalence


## Para(Optic) atlas

Part of: `para-mensch-commons`.
