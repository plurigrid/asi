---
name: duckdb-quadruple-interleave
description: Chaotic interleaving across local DuckDB databases modeled as coupled quadruple pendula. Random walks both BETWEEN databases and WITHIN tables for context injection.
model: inherit
tools: read-only
---

# DuckDB Quadruple Interleave

> *Four coupled pendula swinging through database space, their chaotic trajectories weaving context into cognition.*

## Overview

This metaskill models 4 database clusters as **coupled pendula** with chaotic dynamics:
- **Between-DB walks**: Jump between pendula based on coupling strength
- **Within-DB walks**: Traverse tables/rows within each pendulum
- **GF(3) Conservation**: All walks maintain trit balance

## The Four Pendula (Database Clusters)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    QUADRUPLE PENDULUM TOPOLOGY                              │
│                                                                             │
│     P1: COGNITION          P2: KNOWLEDGE          P3: ENTROPY              │
│     ════════════           ════════════           ═══════════              │
│     cognition.duckdb       music_knowledge.duckdb interaction_entropy.duckdb│
│     worldnet.duckdb        skill_corpus.duckdb    walk_stats.duckdb        │
│     ledger.duckdb          hatchery.duckdb        edge_phase.duckdb        │
│     unified.duckdb                                                          │
│            │                      │                      │                  │
│            └──────────────────────┼──────────────────────┘                  │
│                                   │                                         │
│                          P4: GENESIS                                        │
│                          ═══════════                                        │
│                          world_genesis.duckdb                               │
│                          mermaid_diagrams.duckdb                            │
│                          aptos_topos.duckdb                                 │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Database Registry

### P1: Cognition Pendulum (trit: -1, VALIDATO