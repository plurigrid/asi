---
name: trifurcated-transfer
description: Trifurcated Transfer Skill
model: inherit
tools: read-only
---

# Trifurcated Transfer Skill

```yaml
name: trifurcated-transfer
description: P2P file transfer using 3 parallel subagents over LocalSend HTTP API with GF(3) trit coordination
tags: [p2p, localsend, subagents, file-transfer, tailscale, duckdb, chunking]
version: 1.0.0
author: MINUS
```

## Overview

Trifurcated Transfer implements fault-tolerant P2P file sharing using three parallel subagents, each assigned a trit value from GF(3) (Galois Field of 3 elements). Each subagent attempts transfer over a dedicated channel, providing redundancy and load distribution.

**Core Principles:**
- **Trit Assignment**: MINUS (-1), ERGODIC (0), PLUS (+1)
- **Channel Isolation**: Each trit uses a distinct network path
- **Convergent State**: Transfer succeeds when any channel completes
- **Voice Coordination**: Subagents announce state transitions via `say`

## State Machine

```
┌─────────────────────────────────────────────────────────────────┐
│                    TRIFURCATED TRANSFER FSM                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────┐    spawn 3     ┌──────────────────────────────┐  │
│  │  IDLE    │ ─────────────► │        DISCOVERING           │  │
│  └──────────┘                │  MINUS: Tailscale (100.x.y.z)│  │
│       │                      │  ERGODIC: LAN (192.168.x.y)  │  │
│       │                      │  PLUS: DNS (hostname.local)  │  │
│       │                      └──────────────────────────────┘  │
│       │                                   │                     │
│       │                          all resolved                   │
│       │                                   ▼                     │
│       │                      ┌──────────────────────────────┐  │
│       │                      │        PREPARING             │  │
│       │                      │  POST /prepare-upload        │  │
│       │                      │  Acquire ses