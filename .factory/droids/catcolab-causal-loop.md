---
name: catcolab-causal-loop
description: CatColab Causal Loop Diagrams - systems dynamics modeling with reinforcing (R) and balancing (B) feedback loops, delays, and Lotka-Volterra semantics for strategic analysis.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# CatColab Causal Loop Diagrams: Systems Dynamics

**Trit**: 0 (ERGODIC - coordinator/mediator)
**Color**: Yellow (#FFD700)

## Overview

Causal Loop Diagrams (CLDs) in CatColab model feedback systems:
- **Variables**: System quantities that change over time
- **Positive links (+)**: Same-direction influence (increase→increase)
- **Negative links (-)**: Opposite-direction influence (increase→decrease)
- **Loops**: Reinforcing (R) or Balancing (B) feedback

CLDs are essential for understanding system behavior, policy analysis, and strategic planning.

## Mathematical Foundation

A causal loop diagram is a **signed directed graph** with loop classification:

```
┌─────────────────────────────────────────────────────┐
│            CAUSAL LOOP DIAGRAM                       │
├─────────────────────────────────────────────────────┤
│  Variables:                                          │
│    Population, Resources, Pollution, Quality         │
│                                                      │
│  Positive Links (+):                                 │
│    Population ──(+)──► Pollution                     │
│    Resources ──(+)──► Quality                        │
│                                                      │
│  Negative Links (-):                                 │
│    Pollution ──(-)──► Quality                        │
│    Quality ──(-)──► Population (emigration)          │
│                                                      │
│  Loops:                                              │
│    R1: Population→Births→Population (reinforcing)    │
│    B1: Population→Resources→Quality→Pop (balancing)  │
└─────────────────────────────────────────────────────┘
```

## Loop Classification

**Reinforcing Loop (R)**: Even number of negative links
- Exponential growth or collapse
- "Snowball effect" or "vicious/virtuous cycle"

**Balancing Loop (B)**: Odd number of negative links
- Goal-seeking behavior
- Homeostasis, equilibrium

```
REINFORCING (R):              BA