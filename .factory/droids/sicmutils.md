---
name: sicmutils
description: SICMUtils/Emmy - Clojure library for symbolic mathematics, automatic differentiation, and classical mechanics. Bridges SICM concepts to executable computation via SRFI-compatible abstractions.
model: inherit
tools: ["Read", "Edit", "Execute", "WebSearch"]
---

# SICMUtils (Emmy)

> *"Executable mathematics for computational physics"*
> — Sam Ritchie (mentat-collective)

## Overview

**SICMUtils** (now **Emmy**) is the Clojure implementation of the scmutils library from SICM. It provides:
- Symbolic algebra and simplification
- Automatic differentiation (forward and reverse mode)
- Literal functions and operators
- Lagrangian and Hamiltonian mechanics
- Differential geometry primitives

## SRFI Reachability States

### BEFORE: Disconnected State

```
┌─────────────────────────────────────────────────────────────┐
│  BEFORE SRFI BRIDGE                                          │
├─────────────────────────────────────────────────────────────┤
│  SICMUtils (Clojure)          SRFI (Scheme)                  │
│  ═══════════════════          ═════════════                  │
│  emmy.generic/*               SRFI-1 (lists)     ╳ ISOLATED │
│  emmy.structure/*             SRFI-9 (records)   ╳ ISOLATED │
│  emmy.expression/*            SRFI-27 (random)   ╳ ISOLATED │
│  emmy.calculus/*              SRFI-45 (lazy)     ╳ ISOLATED │
│  emmy.mechanics/*             SRFI-171 (transducers) ╳      │
│                                                              │
│  No compositional path: Clojure ↛ Scheme                     │
│  No GF(3) conservation across language boundary              │
│  No splittable RNG interop                                   │
└─────────────────────────────────────────────────────────────┘
```

### AFTER: Connected State via Cat# Bicomodules

```
┌─────────────────────────────────────────────────────────────┐
│  AFTER SRFI BRIDGE (via Cat# bicomodules)                   │
├─────────────────────────────────────────────────────────────┤
│  SICMUtils (Clojure)          SRFI (Scheme)                  │
│  ═══════════════════          ═════════════                  │
│                                                              │
│  emmy.generic/* ────────────► SRFI-1 (fold/unfold)          │
│       │         Bicomod