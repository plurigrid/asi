---
name: resource-sharing
description: Resource Sharing Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

## CRITICAL: NO DEMOS

Loading this skill ≠ executing demonstration code. Execute ONLY on explicit user request.

# Resource Sharing Skill

> Distribute computational load across machines using GF(3) balanced allocation

## Overview

Resource sharing implements the "all category resource sharing machines" pattern:

- **MINUS (-1)**: Nodes with excess capacity (receivers)
- **ERGODIC (0)**: Coordinator/broker nodes
- **PLUS (+1)**: Nodes with excess load (senders)

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Resource Sharing Mesh                     │
│                                                             │
│  ┌─────────┐      ┌─────────┐      ┌─────────┐             │
│  │ Node A  │◄────►│ Broker  │◄────►│ Node B  │             │
│  │ PLUS +1 │      │ ERGODIC │      │ MINUS -1│             │
│  │ (sender)│      │   (0)   │      │(receiver)│             │
│  └─────────┘      └─────────┘      └─────────┘             │
│       │                                  ▲                  │
│       │         Work Migration           │                  │
│       └──────────────────────────────────┘                  │
│                                                             │
│  GF(3) Invariant: Σ node_trits ≡ 0 (mod 3)                 │
└─────────────────────────────────────────────────────────────┘
```

## Node Classification

```bash
# Determine node trit based on load
node_trit() {
  load=$(uptime | awk -F'load average:' '{print $2}' | cut -d, -f1 | tr -d ' ')
  cpus=$(sysctl -n hw.ncpu 2>/dev/null || nproc)
  ratio=$(echo "$load / $cpus" | bc -l)
  
  if (( $(echo "$ratio > 0.8" | bc -l) )); then
    echo "+1"  # PLUS: overloaded, needs to shed work
  elif (( $(echo "$ratio < 0.3" | bc -l) )); then
    echo "-1"  # MINUS: underloaded, can accept work
  else
    echo "0"   # ERGODIC: balanced
  fi
}
```

## Resource Transfer Protocol

### Via LocalSend
```bash
# Share file to least loaded peer
share_to_