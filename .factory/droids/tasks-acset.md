---
name: tasks-acset
description: Google Tasks management via TasksACSet. Transforms task operations into GF(3)-typed Interactions, routes to triadic queues, detects saturation for task-zero-as-condensed-state.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Tasks ACSet Skill

Transform Google Tasks into an ANIMA-condensed system with GF(3) conservation.

**Trit**: -1 (MINUS - validator)  
**Principle**: Task Zero = Condensed Equilibrium State (all tasks completed)  
**Implementation**: TasksACSet + TriadicQueues + SaturationDetector

## Overview

Tasks ACSet applies the ANIMA framework to task management:

1. **Transform** - Task operations → GF(3)-typed Interactions
2. **Route** - Interactions → Triadic queue fibers (MINUS/ERGODIC/PLUS)
3. **Detect** - Saturation → Task Zero condensed state
4. **Verify** - Narya proofs for consistency

## TasksACSet Schema

```
┌────────────────────────────────────────────────────────────────────┐
│                      TasksACSet Schema                             │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  Interaction ─────┬────▶ Task                                     │
│  ├─ verb: String  │      ├─ task_id: String                       │
│  ├─ timebin: Int  │      ├─ status: {needsAction, completed}      │
│  ├─ trit: Trit    │      ├─ due: Timestamp                        │
│  └─ list ─────────┼──▶   └─ saturated: Bool                       │
│                   │                                                │
│  QueueItem ───────┼────▶ Agent3                                   │
│  ├─ interaction ──┘      ├─ fiber: Trit {-1, 0, +1}               │
│  └─ agent ───────────▶   └─ name: String                          │
│                                                                    │
│  TaskList ◀──────────── Subtask ─────────────────▶ Task           │
│  ├─ list_id: String      ├─ parent_task                           │
│  ├─ title: String        ├─ child_task                            │
│  └─ default: Bool        └─ position: Int                         │
│                                                                    │
│  Completion ─────────────▶ Task           