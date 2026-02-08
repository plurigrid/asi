---
name: markov-game-acset
description: "markov-game-acset skill"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Markov Game ACSet: State-Dependent Open Games

> *"Repeated games are not possible (but Markov games will be soon)"*  
> — [open-games-engine Tutorial](https://github.com/CyberCat-Institute/open-game-engine), line 29

**This skill fills that gap.** Markov games as attributed C-sets with:
- State-dependent strategy spaces
- World operators as information reflow (derangement-constrained)
- GF(3) conservation across state transitions

## Core Insight: Markov Games = Open Games + State ACSet

```
┌─────────────────────────────────────────────────────────────────┐
│  MARKOV GAME = OPEN GAME × STATE CATEGORY                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Standard Open Game:                                            │
│       ┌───────────┐                                             │
│    X ─│           │─ Y    (play: strategies)                    │
│       │  Game G   │                                             │
│    R ←│           │← S    (coplay: utilities)                   │
│       └───────────┘                                             │
│                                                                 │
│  Markov Game adds STATE FUNCTOR:                                │
│       ┌───────────┐        ┌───────────┐                        │
│    X ─│           │─ Y  ───│           │─ X'                    │
│       │  Game G   │        │ Transition│                        │
│    R ←│           │← S  ←──│     T     │← R'                    │
│       └───────────┘        └───────────┘                        │
│            ↓                    ↓                               │
│         State s              State s'                           │
│                                                                 │
│  State transitions follow DERANGEMENT: σ(s) ≠ s                 │
│  No world can observe itself—information MUST reflow            │
│   