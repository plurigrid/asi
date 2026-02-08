---
name: rama-gay-clojure
description: Red Planet Labs Rama with Gay.jl deterministic coloring for 100x backend
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Rama + Gay.jl: Colored Scalable Backends

> *"Build end-to-end backends at any scale in 100x less code — with deterministic color streams."*

## Overview

[Rama](https://redplanetlabs.com/) is a new programming platform by Nathan Marz (creator of Storm) that:
- Reduces backend code by **100x** (10k LOC for Twitter-scale Mastodon)
- Integrates data ingestion, processing, indexing, and querying
- Provides ACID compliance with automatic fault-tolerance

This skill adds Gay.jl 3-color streams for:
1. **Visual debugging** of distributed computations
2. **Deterministic tracing** across shards
3. **Gay-colored parentheses** for S-expression tracking
4. **Tensor shape parallel** expressiveness

## Rama + Gay Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│  RAMA DEPOT (Ingestion)                                         │
│  ┌─────────┐   ┌─────────┐   ┌─────────┐                        │
│  │ Shard 0 │   │ Shard 1 │   │ Shard 2 │                        │
│  │ trit=-1 │   │ trit=0  │   │ trit=+1 │                        │
│  │ #2E86AB │   │ #7CB518 │   │ #FF6B6B │                        │
│  └────┬────┘   └────┬────┘   └────┬────┘                        │
│       │             │             │                              │
│       └─────────────┴─────────────┘                              │
│                     │                                            │
│       ┌─────────────▼─────────────┐                              │
│       │    TOPOLOGY (Processing)   │                              │
│       │    Gay.jl color streams    │                              │
│       └─────────────┬─────────────┘                              │
│                     │                                            │
│       ┌─────────────▼─────────────┐                              │
│       │     PSTATE (Indexing)      │                              │
│       │   Deterministic colors     │                              │
│       └──────────────────────