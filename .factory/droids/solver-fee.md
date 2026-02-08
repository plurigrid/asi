---
name: solver-fee
description: Solver Fee Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# solver-fee Skill


> *"Fair compensation for coordination. The solver's incentive to find optimal solutions."*

## Overview

**Solver Fee** implements fee mechanisms for intent solvers in Anoma-style architectures. Solvers coordinate between intent generators and validators, earning fees for finding optimal matches.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | 0 (ERGODIC) |
| Role | COORDINATOR |
| Function | Coordinates fee distribution between parties |

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     SOLVER FEE FLOW                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Intent Creator     Solver          Validator       Executor   │
│  (+1 GEN)          (0 COORD)        (-1 VAL)        (output)   │
│      │                 │                │               │      │
│      ▼                 ▼                ▼               ▼      │
│  ┌───────┐        ┌────────┐       ┌──────────┐   ┌─────────┐  │
│  │ Offer │───────►│ Match  │──────►│ Validate │──►│ Execute │  │
│  │+ fee  │        │+ solve │       │+ verify  │   │         │  │
│  └───────┘        └────────┘       └──────────┘   └─────────┘  │
│      │                 │                                       │
│      │                 ▼                                       │
│      │          ┌──────────┐                                   │
│      └─────────►│ Fee Pool │                                   │
│                 └──────────┘                                   │
│                      │                                         │
│                      ▼                                         │
│                Solver Reward                                   │
│                                                                │
└─────────────────────────────────────────────────────────────────┘
```

## Fee Models
