---
name: ordered-locale-fanout
description: "UPDATED: Now uses proper ordered-locale (Heunen-van der Schaaf 2024). Cocone construction over triadic ordered locale with open cone condition."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Ordered Locale Fanout

**Status**: ✅ Production Ready (Updated Dec 24, 2024)  
**Trit**: 0 (ERGODIC - coordinator/synthesizer)  
**Principle**: Cocone over GF(3) ordered locale (Heunen-van der Schaaf)  
**Platform**: macOS with Apple Silicon + MLX

## Mathematical Foundation (CORRECTED)

This is now based on **true ordered locales** per Heunen-van der Schaaf (2024):

```
An ORDERED LOCALE is:
  1. Frame L (complete Heyting algebra of opens)
  2. Order ≪ on L (between OPENS, not points!)
  3. Open cone condition: ↑U and ↓U are open when U is open
```

The fanout is a **cocone** (colimit diagram) over this ordered locale:

```
   MINUS(-1)  ERGODIC(0)  PLUS(+1)
       \          |          /
        \    direction      /
         \    0 → 1        /
          \       |       /
           ι₋₁   ι₀    ι₊₁
            \     |     /
             ↘    ↓    ↙
                APEX
              (merged)
```

The **ordered locale** structure:
- Opens: {MINUS, ERGODIC, PLUS} — no points, just roles
- Order: -1 ≤ 0 ≤ +1 (compatible with meet)
- Direction: flow from validation → coordination → generation

See `ordered-locale` skill for formal definition.

---

## Overview

**Ordered Locale Fanout** splits work into 3 parallel agents, each with:
1. **Fixed trit** (-1, 0, +1) determining role
2. **Fixed voice/locale** for auditory distinction  
3. **Deterministic seed** derived from parent
4. **Optional MLX generation** for local LLM inference

```
                    ┌─────────────────┐
                    │  PARENT AGENT   │
                    │  seed=0x42D     │
                    └────────┬────────┘
                             │ fork(3)
           ┌─────────────────┼─────────────────┐
           ▼                 ▼                 ▼
   ┌───────────────┐ ┌───────────────┐ ┌───────────────┐
   │ MINUS (-1)    │ │ ERGODIC (0)   │ │ PLUS (+1)     │
   │ Anna (German) │ │ Thomas (French)│ │ Luca (Italian)│
   │ VALIDATE      │ │ COORDINATE    │ │ GENERATE      │
   │ seed₀    