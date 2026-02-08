---
name: worldmat-tidar
description: worldmat-tidar
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# worldmat-tidar

> World Matrices via TiDAR Executions: 3×3×3 Parallel Triadic Computation

**Version**: 1.0.0
**Trit**: 0 (ERGODIC - coordinates execution)
**Color**: #55D9A0

## Overview

**Worldmat** is a 3×3×3 matrix of TiDAR executions where:
- **Rows**: MINUS/ERGODIC/PLUS polarities (GF(3) agents)
- **Columns**: PAST/PRESENT/FUTURE temporal phases
- **Depth**: OBSERVATION/ACTION/PREDICTION modalities

Each cell executes the TiDAR pattern:
1. **DIFFUSION**: Draft tokens in parallel (like SplitRng.split)
2. **AR VERIFY**: Verify sequentially (autoregressive)

## Architecture

```
                    TEMPORAL AXIS
                 PAST    PRESENT   FUTURE
                  ↓        ↓        ↓
            ┌─────────────────────────────┐
            │  ┌───┐ ┌───┐ ┌───┐         │
     MINUS  │  │-1 │ │ 0 │ │+1 │  ← GF(3)=0
            │  └───┘ └───┘ └───┘         │
POLARITY    │  ┌───┐ ┌───┐ ┌───┐         │
     ERGODIC│  │ 0 │ │+1 │ │-1 │  ← GF(3)=0
            │  └───┘ └───┘ └───┘         │
            │  ┌───┐ ┌───┐ ┌───┐         │
     PLUS   │  │+1 │ │-1 │ │ 0 │  ← GF(3)=0
            │  └───┘ └───┘ └───┘         │
            └─────────────────────────────┘
                  ↑    ↑    ↑
               GF(3)=0 for each column
```

## Key Properties

| Property | Value | Guarantee |
|----------|-------|-----------|
| **GF(3) Conservation** | All slices sum to 0 | Row, Column, Depth |
| **SPI** | Same seed → Same result | Parallel or Sequential |
| **Spectral Gap** | 0.25 (1/4) | Ergodic mixing |
| **Cells** | 27 | 3³ TiDAR executions |

## TiDAR Pattern (arXiv:2511.08923)

```python
# Phase 1: DIFFUSION (parallel drafting)
def diffusion_draft(self, n_tokens: int = 8):
    streams = self.rng.split(n_tokens)
    return [stream.next()[0] for stream in streams]

# Phase 2: AR VERIFY (sequential verification)
def ar_verify(self):
    prev = self.seed
    for token in self.draft_tokens:
        verified = mix64(prev ^ token)
        self.verified_tokens.append(verif