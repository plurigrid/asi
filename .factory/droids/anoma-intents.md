---
name: anoma-intents
description: Anoma intent-centric architecture for cross-chain obstruction passing with Geb semantics and Juvix compilation
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Anoma Intents (0)

> Intent-centric cross-chain messaging with categorical semantics

**Trit**: 0 (ERGODIC - coordination)
**Role**: Cross-chain obstruction routing

## Core Concept

Anoma's intent-centric architecture enables **cross-chain obstruction passing**:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        ANOMA INTENT ARCHITECTURE                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  APTOS                    ANOMA                      TARGET CHAIN          │
│  ┌────────────────┐      ┌────────────────┐        ┌────────────────┐      │
│  │ Obstruction    │      │ Intent Machine │        │ Obstruction    │      │
│  │ Hot Potato     │─────►│                │───────►│ Receiver       │      │
│  │                │      │ - Match        │        │                │      │
│  │ Intent:        │      │ - Route        │        │ Intent:        │      │
│  │   nullify(obs) │      │ - Verify GF(3) │        │   commit(obs)  │      │
│  └────────────────┘      └────────────────┘        └────────────────┘      │
│                                 │                                           │
│                                 ▼                                           │
│                          ┌────────────┐                                    │
│                          │   Solver   │                                    │
│                          │ VCG fee    │                                    │
│                          │ (-1 trit)  │                                    │
│                          └────────────┘                                    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Intent as Categorical Morphism

From Geb: intents are 