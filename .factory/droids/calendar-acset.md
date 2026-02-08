---
name: calendar-acset
description: Google Calendar management via CalendarACSet. Transforms scheduling operations into GF(3)-typed Interactions, routes to triadic queues, detects saturation for balanced-calendar-as-condensed-state.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Calendar ACSet Skill

Transform Google Calendar into an ANIMA-condensed system with GF(3) conservation.

**Trit**: +1 (PLUS - generator/executor)  
**Principle**: Balanced Calendar = Condensed Equilibrium State  
**Implementation**: CalendarACSet + TriadicQueues + SaturationDetector

## Overview

Calendar ACSet applies the ANIMA framework to scheduling:

1. **Transform** - Events → GF(3)-typed Interactions
2. **Route** - Interactions → Triadic queue fibers (MINUS/ERGODIC/PLUS)
3. **Detect** - Saturation → Balanced calendar state
4. **Verify** - Narya proofs for scheduling consistency

## CalendarACSet Schema

```
┌────────────────────────────────────────────────────────────────────┐
│                     CalendarACSet Schema                           │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  Interaction ─────┬────▶ Event                                     │
│  ├─ verb: String  │      ├─ event_id: String                       │
│  ├─ timebin: Int  │      ├─ summary: String                        │
│  ├─ trit: Trit    │      ├─ start_time: DateTime                   │
│  └─ calendar ─────┼──▶   ├─ end_time: DateTime                     │
│                   │      ├─ has_conflicts: Bool                    │
│  QueueItem ───────┼──▶   └─ saturated: Bool                        │
│  ├─ interaction ──┘                                                │
│  └─ agent ───────────▶ Agent3                                      │
│                        ├─ fiber: Trit {-1, 0, +1}                  │
│  Attendee ◀────────────┤                                           │
│  ├─ email: String      └─ name: String                             │
│  ├─ response: Enum                                                 │
│  └─ event ─────────▶ Event                                         │
│                                                                    │
│  Reminder ─────────▶ Event