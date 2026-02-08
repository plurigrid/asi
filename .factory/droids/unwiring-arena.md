---
name: unwiring-arena
description: Play/Coplay arena theory for autopoietic closure with GF(3) conservation
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Unwiring Arena Skill

**Status**: ✅ Production Ready  
**Trit**: 0 (ERGODIC - balanced flow)  
**Principle**: Play/Coplay autopoietic closure with GF(3) conservation  
**Source**: plurigrid/UnwiringDiagrams.jl#1 + Capucci et al. Arena Theory

---

## Overview

**Unwiring Arena** unifies three categorical patterns:

1. **Wiring Diagrams** (AlgebraicJulia/Catlab) - Compositional system construction
2. **Unwiring Rules** (GayUncommonsSimulator) - Learning through constraint release
3. **Arena Protocol** (Plurigrid Amelia v0.4) - Play/Coplay bidirectional channels

```
┌─ Play Channel (Outbound) ─────────────────┐
│ Local arena mutations → NATS broadcast    │
│ Strategy profiles → Action selection      │
└────────────────────────────────────────────┘
                    ↕ (Autopoietic closure)
┌─ Coplay Channel (Inbound) ───────────────┐
│ Peer arena submissions → Reconciliation   │
│ Rewards/feedback → Identity update        │
└────────────────────────────────────────────┘
```

## Mathematical Foundation

### Arenas as Parametrised Lenses

From Capucci, Ghani, Ledent, Forsberg:

```
Arena A_G : Lens_{(Ω,℧)}(X,S)(Y,R)

where:
  Ω = Π_{p∈P} Ωₚ     (strategy profiles)
  ℧ = Π_{p∈P} ℧ₚ     (reward vectors)
  X, Y = states
  S, R = costates (feedback)
```

**Play**: `play_A : Ω × X → Y` (forward pass)
**Coplay**: `coplay_A : Ω × X × R → ℧ × S` (backward pass with feedback)

### Unwiring = Learning Through Constraint Release

```julia
struct UnwiringRule
    source_gf3::Int         # Source polarity {-1, 0, +1}
    target_gf3::Int         # Target polarity
    learning_rate::Float64  # How fast to unwire
    threshold::Float64      # Discrepancy threshold to trigger
end

# Unwiring shifts internal toward external (learning)
function apply_unwiring(rule, internal, external)
    α = rule.learning_rate
    return (1-α) * internal + α * external
end
```

### GF(3) Tripartite Channels

```
MINUS (-1)   : Constraint verification (coplay focus)
ERGODIC (0)  : Balance/coordination