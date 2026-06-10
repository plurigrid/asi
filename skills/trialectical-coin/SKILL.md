---
name: trialectical-coin
description: Extends TeglonLabs/coin-flip-mcp with GF(3) ternary decision logic.
metadata:
  interface_ports:
  - References
  - Integration with
trit: 0
---
# Trialectical Coin Skill

Extends TeglonLabs/coin-flip-mcp with GF(3) ternary decision logic.

## Source
- **Repository**: [TeglonLabs/coin-flip-mcp](https://github.com/TeglonLabs/coin-flip-mcp)
- **Trit**: 0 (ERGODIC - meta-decision coordinator)

## Overview

The trialectical coin replaces binary true/false with ternary −/○/+ outcomes:

| Outcome | Trit | Meaning | Action |
|---------|------|---------|--------|
| Heads | +1 | PLUS | Generate, create, affirm |
| _ | 0 | ERGODIC | Defer, observe, coordinate |
| Tails | −1 | MINUS | Validate, verify, negate |

## GF(3) Conservation

Every trialectical flip maintains conservation:
- Single flip: outcome ∈ {−1, 0, +1}
- Triple flip: Σ(outcomes) ≡ 0 (mod 3) when balanced
- Meta-decisions use the ERGODIC outcome to defer to oracle

## MCP Tools

### `trialectical_flip`
Flip a 3-sided coin with GF(3) semantics.

```json
{
  "name": "trialectical_flip",
  "arguments": {
    "seed": 1069,
    "context": "Should I generate or validate?"
  }
}
```

**Returns**:
```json
{
  "outcome": "+",
  "trit": 1,
  "meaning": "PLUS: Generate, create, affirm",
  "color": "#E67F86",
  "gf3_balanced": true
}
```

### `trialectical_batch`
Flip N coins, ensuring GF(3) conservation.

```json
{
  "name": "trialectical_batch",
  "arguments": {
    "count": 6,
    "seed": 1069
  }
}
```

**Returns**:
```json
{
  "outcomes": ["+", "−", "○", "+", "−", "○"],
  "trits": [1, -1, 0, 1, -1, 0],
  "sum": 0,
  "conserved": true
}
```

### `trialectical_oracle`
Meta-decision: flip until reaching consensus (3 same outcomes).

```json
{
  "name": "trialectical_oracle",
  "arguments": {
    "question": "Which skill to invoke?",
    "options": ["narya-proofs", "gay-mcp", "bisimulation-game"]
  }
}
```

## Ising State Model

The trialectical coin implements an Ising model where:
- Spins: σᵢ ∈ {−1, 0, +1}
- Energy: E = −J Σ σᵢσⱼ (ferromagnetic coupling)
- Temperature: τ controls randomness vs determinism

At τ=0: Deterministic (same seed → same outcome)
At τ→∞: Maximum entropy (equal probability)
At τ=τ*: Critical point (BKT transition)

## Usage Patterns

### Decision Branching
```
flip = trialectical_flip()
if flip.trit == 1:
    # PLUS: Generate new content
elif flip.trit == -1:
    # MINUS: Validate existing content
else:
    # ERGODIC: Defer to oracle or user
```

### Triadic Task Assignment
```
flips = trialectical_batch(3)
# Assign to subagents based on trit:
# flips[1] → MINUS validator
# flips[2] → ERGODIC coordinator  
# flips[3] → PLUS generator
```

### GF(3)-Balanced Exploration
```
# Ensure sum of decisions = 0 (mod 3)
while not conserved:
    flips = trialectical_batch(n)
    if sum(flips.trits) % 3 == 0:
        conserved = true
```

## Random.org Integration

For true randomness (not pseudo-random):
1. Query random.org for integer in [0, 2]
2. Map: 0 → −1 (Tails), 1 → 0 (_), 2 → +1 (Heads)
3. Cache for offline use with Gay.jl fallback

## Skill Correspondences

| Outcome | Skill Pattern | Example |
|---------|---------------|---------|
| PLUS (+1) | Generation | `gay-mcp`, `free-monad-gen` |
| ERGODIC (0) | Coordination | `bisimulation-game`, `duckdb-ies` |
| MINUS (−1) | Validation | `narya-proofs`, `cybernetic-immune` |

## Installation

```bash
# Clone TeglonLabs repo
git clone https://github.com/TeglonLabs/coin-flip-mcp
cd coin-flip-mcp
npm install
npm run build

# Add to Claude config
# ~/.config/claude/claude_desktop_config.json
```

## Configuration

```json
{
  "mcpServers": {
    "trialectical-coin": {
      "command": "node",
      "args": ["/path/to/coin-flip-mcp/build/index.js"],
      "env": {
        "RANDOM_ORG_API_KEY": "your-key-here"
      }
    }
  }
}
```

---

## End-of-Skill Interface

## Integration with Gay.jl

```julia
using Gay

# Seed from gay_seed for reproducibility
gay_seed!(1069)

# Flip using Gay.jl color-to-trit mapping
color = gay_color_at(42)
trit = gay_trit_at(42)  # Derived from hue

outcome = trit == 1 ? "Heads" : trit == -1 ? "Tails" : "_"
```

## References

- [AIP-41](https://aptos.dev/build/smart-contracts/randomness) - Aptos on-chain randomness
- [Gay.jl](https://github.com/bmorphism/Gay.jl) - Deterministic color generation
- [Ising Model](https://en.wikipedia.org/wiki/Ising_model) - Statistical mechanics basis
- [GF(3)](https://en.wikipedia.org/wiki/GF(3)) - Field with 3 elements


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
