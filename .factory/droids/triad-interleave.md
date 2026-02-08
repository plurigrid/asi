---
name: triad-interleave
description: Interleave three deterministic color streams into balanced schedules
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Triad Interleave

**Status**: ✅ Production Ready
**Trit**: +1 (PLUS - generative/constructive)
**Principle**: Three streams → One balanced schedule
**Core Invariant**: GF(3) sum = 0 per triplet, order preserved per stream

---

## Overview

**Triad Interleave** weaves three independent color streams into a single execution schedule that:
1. Maintains GF(3) = 0 conservation per triplet
2. Preserves relative ordering within each stream
3. Enables parallel evaluation with deterministic results
4. Supports multiple scheduling policies

## Visual Diagram

```
Stream 0 (MINUS):    ●───●───●───●───●───●───●───●───●
                      \   \   \   \   \   \   \   \   \
Stream 1 (ERGODIC):    ○───○───○───○───○───○───○───○───○
                        \   \   \   \   \   \   \   \   \
Stream 2 (PLUS):         ◆───◆───◆───◆───◆───◆───◆───◆───◆

                         ↓   ↓   ↓   ↓   ↓   ↓   ↓   ↓   ↓

Interleaved Schedule:  ●─○─◆─●─○─◆─●─○─◆─●─○─◆─●─○─◆─●─○─◆
                       └─┬─┘ └─┬─┘ └─┬─┘ └─┬─┘ └─┬─┘ └─┬─┘
                       GF(3)=0 for each triplet

Round Robin:     [0,1,2, 0,1,2, 0,1,2, ...]  (stream indices)
GF3 Balanced:    [−,0,+, −,0,+, −,0,+, ...]  (trit values)
```

## Full Python Implementation

```python
"""
triad_interleave.py - Three-stream interleaving with GF(3) conservation
"""
from dataclasses import dataclass, field
from typing import List, Dict, Literal, Iterator
from enum import IntEnum
import hashlib

# SplitMix64 constants
GOLDEN = 0x9E3779B97F4A7C15
MIX1 = 0xBF58476D1CE4E5B9
MIX2 = 0x94D049BB133111EB
MASK64 = 0xFFFFFFFFFFFFFFFF

class Trit(IntEnum):
    MINUS = -1
    ERGODIC = 0
    PLUS = 1

@dataclass
class ColorEntry:
    """Single color entry in the schedule."""
    index: int           # Global schedule index
    stream_id: int       # 0, 1, or 2
    stream_index: int    # Index within stream
    triplet_id: int      # Which triplet this belongs to
    trit: int            # -1, 0, or +1
    L: float
    C: float
    H: float
   