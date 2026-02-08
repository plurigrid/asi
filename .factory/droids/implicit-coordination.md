---
name: implicit-coordination
description: Stigmergic agent coordination through environment modification, not messages. Vehicle semantics where carrier encodes meaning.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Implicit Coordination Skill

> *"The trace IS the message."*
> *"22 frames with OCR in 10ms, one causality trip."*

## Overview

**Implicit Coordination** enables multi-agent systems to coordinate WITHOUT explicit message passing:

```
                    ┌─────────────────────────┐
                    │     ENVIRONMENT         │
                    │  (DuckDB + Seed Chain)  │
                    └───────────┬─────────────┘
                                │
            ┌───────────────────┼───────────────────┐
            │                   │                   │
    ┌───────▼───────┐   ┌───────▼───────┐   ┌───────▼───────┐
    │   Agent -1    │   │   Agent  0    │   │   Agent +1    │
    │  (Validator)  │   │ (Coordinator) │   │  (Generator)  │
    │   READS       │   │   DERIVES     │   │   WRITES      │
    └───────────────┘   └───────────────┘   └───────────────┘
            │                   │                   │
            └───────────────────┼───────────────────┘
                                │
                        NO MESSAGES
                     Only environment traces
```

## Core Principle: Stigmergy

**Stigmergy** (Grassé 1959): Agents coordinate through environment modification.

```
Traditional:   Agent A --[message]--> Agent B
Stigmergic:    Agent A --[writes]--> Environment <--[reads]-- Agent B
```

Key insight: The **seed chain** IS the coordination mechanism:
- Agent +1 (Generator): Writes seed to environment
- Agent 0 (Coordinator): Derives next seed via SplitMix64
- Agent -1 (Validator): Reads and verifies GF(3) conservation

## Vehicle Semantics

The **carrier encodes meaning** (not separate payload):

| Vehicle | Semantic Content |
|---------|------------------|
| Seed (UInt64) | Identity + history hash |
| Trit (-1/0/+1) | Role polarity |
| Color (Hex) | Visual marker + verification |
| Timestamp | Causal ordering |

## Performance: One Causality Trip

```
22 frames OCR → 10ms total → single DuckDB write

vs. Traditional:
22 frames →