---
name: protocol-evolution-markets
description: Prediction markets for protocol standard evolution. Bet on which specs survive, fork, or merge using multiverse finance and GF(3) fitness signals.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Protocol Evolution Markets

**Trit**: 0 (ERGODIC - coordinates market equilibrium)  
**Foundation**: Dave White Multiverse Finance + Skill Evolution + Mixing Proofs

## Core Concept

Protocol standards evolve through selection pressure. Prediction markets provide:
1. **Price signals** for which standards will be adopted
2. **Incentive alignment** for standard development
3. **Fork coordination** when communities disagree
4. **Merge signals** when standards converge

```
┌─────────────────────────────────────────────────────────────────────┐
│                    PROTOCOL EVOLUTION MARKET                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   Standard A ──┬── Fork A.1 ──┬── Merge AB ◄── Standard B          │
│                │              │                    │                │
│                └── Fork A.2   └── Dead End         └── Fork B.1    │
│                                                                     │
│   Market prices predict which branches survive                      │
└─────────────────────────────────────────────────────────────────────┘
```

## Multiverse Finance Integration

From Dave White's paper: split financial system into parallel universes (verses).

### Verses as Protocol Futures

```julia
# Each verse represents a possible protocol future
struct ProtocolVerse
    spec_hash::UInt64           # Hash of specification
    adoption_metric::Float64    # Current adoption (0-1)
    compatibility::Set{Symbol}  # Compatible protocols
    parent_verse::Union{Nothing, ProtocolVerse}
end

# Example: agentskills.io spec versions
verses = [
    ProtocolVerse(hash("v1.0"), 0.8, Set([:claude, :codex]), nothing),
    ProtocolVerse(hash("v1.1"), 0.3, Set([:claude, :codex, :cursor]), v1_0),
    ProtocolVerse(hash("v2.0-draft"), 0.1, Set([:amp]), v1_0),
]
```

### Push Down / Pull Up Operations

```julia
# Push down: bet on ALL forks of a