---
name: bisimulation-game
description: Bisimulation game for resilient skill dispersal across AI agents with
model: inherit
tools: read-only
---

# Bisimulation Game Skill

> *"Two systems are bisimilar if they cannot be distinguished by any observation."*

## Overview

The bisimulation game provides a framework for:
1. **Resilient skill dispersal** across multiple AI agents
2. **GF(3) conservation** during state transitions
3. **Observational bridge types** for version-aware synchronization
4. **Self-rewriting capabilities** via MCP Tasks protocol

## Narya's `isBisim` Foundation

This skill implements the game-theoretic interpretation of Narya's `isBisim` coinductive type:

```narya
def isBisim (A B : Type) (R : A → B → Type) : Type ≔ codata [
| x .trr : A → B                              -- Attacker: transition A→B
| x .liftr : (a : A) → R a (x .trr a)         -- Defender: lift preserves R
| x .trl : B → A                              -- Attacker: transition B→A
| x .liftl : (b : B) → R (x .trl b) b         -- Defender: lift preserves R
| x .id.e                                      -- Arbiter: higher coherence
  : (a0 : A.0) (b0 : B.0) (r0 : R.0 a0 b0) (a1 : A.1) (b1 : B.1) (r1 : R.1 a1 b1)
    → isBisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ R.2 a0 a1 a2 b0 b1 b2 r0 r1) ]
```

### Game-Theoretic Interpretation

| Narya Field | Game Role | Trit | Description |
|-------------|-----------|------|-------------|
| `.trr` | Attacker move | -1 | Forward transition challenge |
| `.liftr` | Defender response | +1 | Prove relation preserved |
| `.trl` | Attacker move | -1 | Backward transition challenge |
| `.liftl` | Defender response | +1 | Prove relation preserved |
| `.id.e` | Arbiter | 0 | Recursive coherence at identity types |

**Univalence**: If Defender can always respond → `glue A B R Rb : Id Type A B`

## Game Rules

### Players

| Player | Role | Trit | Color |
|--------|------|------|-------|
| Attacker | Tries to distinguish systems | -1 | Blue |
| Defender | Maintains equivalence | +1 | Red |
| Arbiter | Verifies conservation | 0 | Green |

### Moves

```
┌─────────────────────────────────────────────────