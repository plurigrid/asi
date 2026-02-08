---
name: gmail-anima
description: Gmail inbox management via ANIMA condensation. Transforms messages into GF(3)-typed Interactions, routes to triadic queues, detects saturation for inbox-zero-as-condensed-state. Use for email triage, workflow automation, or applying ANIMA principles to Gmail.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Gmail ANIMA Skill

Transform Gmail into an ANIMA-condensed system with GF(3) conservation.

**Trit**: 0 (ERGODIC - coordinator)  
**Principle**: Inbox Zero = Condensed Equilibrium State  
**Implementation**: GmailACSet + TriadicQueues + AnimaDetector

## Overview

Gmail ANIMA applies the ANIMA framework to email:

1. **Transform** - Messages → GF(3)-typed Interactions
2. **Route** - Interactions → Triadic queue fibers (MINUS/ERGODIC/PLUS)
3. **Detect** - Saturation → ANIMA condensed state
4. **Verify** - Narya proofs for consistency

## GmailACSet Schema

```
┌────────────────────────────────────────────────────────────────────┐
│                      GmailACSet Schema                             │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  Interaction ─────┬────▶ Thread                                   │
│  ├─ verb: String  │      ├─ thread_id: String                     │
│  ├─ timebin: Int  │      ├─ needs_action: Bool                    │
│  ├─ trit: Trit    │      ├─ last_action_bin: Int                  │
│  └─ person ───────┼──▶   └─ saturated: Bool                       │
│                   │                                                │
│  QueueItem ───────┼────▶ Agent3                                   │
│  ├─ interaction ──┘      ├─ fiber: Trit {-1, 0, +1}               │
│  └─ agent ───────────▶   └─ name: String                          │
│                                                                    │
│  Person ◀─────────────── Partner ────────────────▶ Person         │
│  ├─ email: String        ├─ src                                   │
│  └─ name: String         ├─ tgt                                   │
│                          └─ weight: Int                            │
└────────────────────────────────────────────────────────────────────┘
```

### Objects

| Object | Description | Trit Role |
|--------|-------------|-----------|
| 