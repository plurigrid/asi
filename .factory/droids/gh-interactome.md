---
name: gh-interactome
description: GitHub author interaction network discovery. Maps cobordisms between
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# gh-interactome - GitHub Author Interaction Network

## Overview

Maps the **interactome** (interaction network) of GitHub contributors across discovered repos. Finds **cobordisms** - shared boundaries where different research communities meet.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         INTERACTOME STRUCTURE                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│   BlockScience ◄────── olynch ──────► ToposInstitute                        │
│        │                  │                  │                               │
│        ▼                  ▼                  ▼                               │
│     cadCAD         AlgebraicJulia        poly                               │
│        │                  │                  │                               │
│        └──── jpfairbanks ─┴── epatters ─────┘                               │
│                                                                              │
│   HoTT/Coq-HoTT ◄─── abooij ───► mortberg/cubicaltt                         │
│        │                                     │                               │
│        └────── mikeshulman ──────────────────┘                               │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Discovered Cobordisms

### Cobordism 1: AlgebraicJulia ↔ Topos Institute ↔ BlockScience

**Shared contributors:**
- `epatters` (Evan Patterson) - Catlab.jl, ACSets.jl, Topos Institute
- `olynch` (Owen Lynch) - poly, ACSets.jl, Catlab.jl, Topos Institute
- `jpfairbanks` (James Fairbanks) - Catlab.jl, ACSets.jl, U Florida
- `kris-brown` - Catlab.jl, ACSets.jl, Topos Institute
- `slibkind` (Sophie Libkind) - Catlab.jl, Stanford/Topos

**Bridge re