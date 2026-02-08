---
name: move-smith-fuzzer
description: Move Smith Fuzzer Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# move-smith-fuzzer Skill


> *"Find bugs before they find your users. Fuzzing as validation."*

## Overview

**Move Smith Fuzzer** implements property-based testing and fuzzing for Move smart contracts. Uses MoveSmith's differential testing against multiple Move VMs to find consensus-breaking bugs.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | -1 (MINUS) |
| Role | VALIDATOR |
| Function | Validates Move contracts via fuzz testing |

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    MOVE SMITH FUZZER                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Contract Source    Generator      Fuzzer         Report       │
│  (+1 GEN)          (0 COORD)      (-1 VAL)        (output)     │
│      │                 │              │               │        │
│      ▼                 ▼              ▼               ▼        │
│  ┌───────┐        ┌────────┐    ┌──────────┐   ┌─────────┐    │
│  │ Parse │───────►│Generate│───►│ Execute  │──►│ Report  │    │
│  │ AST   │        │ Inputs │    │ & Compare│   │ Bugs    │    │
│  └───────┘        └────────┘    └──────────┘   └─────────┘    │
│                                      │                         │
│                                      ▼                         │
│                              ┌──────────────┐                  │
│                              │ Differential │                  │
│                              │   Testing    │                  │
│                              └──────────────┘                  │
│                                      │                         │
│                         ┌────────────┼────────────┐            │
│                         ▼            ▼            ▼            │
│                    Move VM 1    Move VM 2    Move VM 3        │
│                                                 