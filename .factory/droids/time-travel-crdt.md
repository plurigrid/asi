---
name: time-travel-crdt
description: Time Travel CRDT Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Time Travel CRDT Skill

> *"Time is of the essence — but the essence is not time."*
> — Kleppmann & Gentle

CRDTs enable time travel: branch, merge, undo, redo without central coordination. GF(3) coloring for causal consistency.

## Overview

Time travel in collaborative systems means:
1. **Branching**: Diverge from any point in history
2. **Merging**: Automatically reconcile divergent branches
3. **Undo/Redo**: Navigate the causal graph
4. **Replay**: Reconstruct any historical state

This skill connects Diamond Types, Automerge, Eg-walker, and Janus reversible computing.

## Core Algorithms

### Eg-walker (Gentle & Kleppmann 2025) [ERGODIC: 0]

The **Event Graph Walker** combines the best of OT and CRDTs:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         EG-WALKER ARCHITECTURE                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│   Operation Log          Event Graph              Current State              │
│   ┌──────────┐          ┌───────────┐            ┌───────────┐              │
│   │ Insert A │──────────│  A ───┐   │            │           │              │
│   │ Insert B │          │       ▼   │            │  "ABCD"   │              │
│   │ Delete C │──────────│  B ◄── D  │────────────│           │              │
│   │ Insert D │          │       ▲   │            └───────────┘              │
│   └──────────┘          │  C ───┘   │                                       │
│                         └───────────┘                                       │
│                                                                              │
│   Time Complexity:                                                           │
│   - Insert/Delete: O(log n) amortized                                       │
│   - Merge: O(n) worst case, O(1) common case                         