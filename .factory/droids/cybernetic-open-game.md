---
name: cybernetic-open-game
description: Cybernetic Open Game Skill
model: inherit
tools: read-only
---

# Cybernetic Open Game Skill

> Compositional game theory for off-chain/on-chain cybernetic feedback loops with GF(3) Nash equilibrium

**Trit**: 0 (ERGODIC - Coordinator)
**Color**: #26D826 (Green)
**Status**: Production Ready
**Created**: 2025-12-30

## Overview

This skill formalizes the **Agent-O-Rama ↔ Worldnet ↔ STC** cybernetic feedback loop as a compositional open game where:

- **Off-chain intelligence** (Agent-O-Rama/DuckDB) drives cognition
- **On-chain settlement** (Secure Ternary Coin/Aptos) provides finality
- **Value-conserving bridge** (Worldnet) maintains GF(3) balance
- **Nash equilibrium** = GF(3) conservation across all layers

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    CYBERNETIC LOOP AS OPEN GAME                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│         FORWARD PLAY (Strategies)                                           │
│                                                                             │
│    Intent ──────────▶ Transaction ──────────▶ Settlement                    │
│      X                    Y                      Z                          │
│                                                                             │
│    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐                   │
│    │ Agent-O-Rama│───▶│  Worldnet   │───▶│    STC      │                   │
│    │   (-1)      │    │    (0)      │    │   (+1)      │                   │
│    │   PLAY      │    │   VERIFY    │    │   SETTLE    │                   │
│    └─────────────┘    └─────────────┘    └─────────────┘                   │
│          ▲                  │                  │                            │
│          │                  │                  │                            │
│          │    BACKWARD COPLAY (Utilities)      │               