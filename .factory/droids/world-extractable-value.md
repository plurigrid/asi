---
name: world-extractable-value
description: Extract value from world transitions via Markov blanket arbitrage. WEV = PoA - 1. Paradigm Multiverse Finance integration.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# World Extractable Value (WEV) Skill

> *"The gap between Nash and Optimal is not waste -- it is extractable value."*
> *"Multiverse Finance splits the financial system into parallel universes."* -- Dave White, Paradigm

## Overview

**World Extractable Value** quantifies the inefficiency extractable from selfish equilibria, integrated with Paradigm's Multiverse Finance thesis:

```
WEV = Price of Anarchy - 1 = (C_Nash / C_Opt) - 1
```

This bridges:
- **Friston's Free Energy**: Minimize surprise via inference
- **Roughgarden's PoA**: Bound selfish routing inefficiency
- **Badiou's World-Hopping**: Events extract truth from being

## Core Formula

```
                    ┌─────────────────────────┐
                    │     WORLD W₁ (Nash)     │
                    │     Cost = C_Nash       │
                    └───────────┬─────────────┘
                                │
                          ┌─────▼─────┐
                          │  MARKOV   │
                          │  BLANKET  │
                          │  (Event)  │
                          └─────┬─────┘
                                │
                    ┌───────────▼─────────────┐
                    │    WORLD W₂ (Optimal)   │
                    │     Cost = C_Opt        │
                    └─────────────────────────┘

    WEV = C_Nash - C_Opt = C_Opt × (PoA - 1)
```

## Components

### 1. Price of Anarchy (Roughgarden)

For d-regular Ramanujan expanders:

```
PoA = 1 + 1/gap = 1 + 1/(d - 2√(d-1))

d=4: PoA = 1 + 1/0.536 ≈ 2.87
```

### 2. Free Energy (Friston)

```
F = E_q[log q(x) - log p(x,y)]
  = Prediction_Error + Model_Complexity
  
F ≈ 1/gap + 0.1 ≈ 1.96
```

### 3. Markov Blanket

The boundary between self and world:
- **Sensory states**: Observations from world
- **Active states**: Actions on world
- **Internal states**: Agent's model

### 4. Action Direction

| Condition | Strategy | Effect |
|-----------|----------|--------|
| Error > 0.5 | Perceptual Inference | Update beliefs |
|