---
name: gworkspace-mcp
description: gworkspace-mcp - Google Workspace MCP Integration with Temporal Consistency
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# gworkspace-mcp - Google Workspace MCP Integration with Temporal Consistency

## Overview

Integrates Google Workspace services (Gmail, Drive, Calendar, Docs, Sheets, Tasks, Meet) through MCP with:

1. **Causal Poset Interaction Time**: First-class temporal structure for replay determinism
2. **GF(3) Triadic Conservation**: Every action classified as PLUS (+1), ERGODIC (0), or MINUS (-1)
3. **Cross-Service Atomicity**: Two-phase commit for multi-service workflows
4. **ANIMA Condensation**: Saturation states (Inbox Zero, Task Zero) as fixed points
5. **Retry with 1069 Checkpoints**: Balanced ternary error recovery

**Trit**: 0 (ERGODIC) - Coordinates cross-service workflows

## Core Formula

```
InteractionTime ≅ CausalPoset(Events)
GlobalSaturation = (∀s. ServiceSaturated s) ∧ CrossServiceConsistent ∧ TemporalClosure ∧ (Σ trits = 0)
FreeTrace ⊣ CondensedInteractionTime  -- Temporal adjunction
```

## Predicates

| Predicate | Description | GF(3) Role |
|-----------|-------------|------------|
| `CausallyPrecedes(e₁, e₂)` | e₁ causally before e₂ | Order structure |
| `Concurrent(e₁, e₂)` | Neither precedes the other | Concurrency |
| `ServiceSaturated(s)` | No pending operations | Local stability |
| `CrossServiceConsistent(g)` | All dependencies resolved | Global consistency |
| `TemporalClosure(g)` | All consequences computed | Causal completeness |
| `GlobalSaturation(g)` | Full condensation achieved | Fixed point |
| `InboxZero(gmail)` | All emails processed | Domain saturation |
| `TaskZero(tasks)` | All tasks completed | Domain saturation |

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                    Google Workspace MCP Integration                              │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   Services                    Causal Layer                    Con