---
name: spi-parallel-verify
description: Verify Strong Parallelism Invariance (SPI) and GF(3) conservation for
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# SPI Parallel Verify

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - verification/neutral)
**Principle**: Execution order does not affect results
**Core Invariant**: `color(seed, i) == color(seed, i)` regardless of computation path

---

## Overview

**Strong Parallelism Invariance (SPI)** guarantees that deterministic color streams produce identical results whether computed:
- Sequentially (indices 0, 1, 2, ...)
- In reverse (indices ..., 2, 1, 0)
- Shuffled (indices in any permutation)
- In parallel (multiple threads/processes)

This skill verifies SPI and GF(3) conservation across implementations.

## Theoretical Foundation

```
SPI Theorem: For any deterministic generator G with seed s,
             ∀ permutation π of indices I:
             G(s, I) ≡ G(s, π(I)) (modulo ordering)

GF(3) Conservation: For tripartite streams,
                    ∀ triplet t: sum(t.trits) ≡ 0 (mod 3)
```

## Full Python Implementation

```python
"""
spi_verify.py - Strong Parallelism Invariance Verification
"""
import random
from dataclasses import dataclass
from typing import List, Dict, Tuple
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor

# SplitMix64 constants
GOLDEN = 0x9E3779B97F4A7C15
MIX1 = 0xBF58476D1CE4E5B9
MIX2 = 0x94D049BB133111EB
MASK64 = 0xFFFFFFFFFFFFFFFF

def splitmix64(state: int) -> Tuple[int, int]:
    """Single SplitMix64 step. Returns (next_state, output)."""
    state = (state + GOLDEN) & MASK64
    z = state
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    return state, z ^ (z >> 31)

def color_at(seed: int, index: int) -> Dict:
    """Compute color at index deterministically (O(1) via jump)."""
    # Jump to index position
    state = (seed + GOLDEN * index) & MASK64
    _, z1 = splitmix64(state)
    state, z2 = splitmix64(state)
    _, z3 = splitmix64(state)
    
    # Map to OkLCH
    L = 10 + (z1 / MASK64) * 85
    C = (z2 / MASK64) * 100
    H = (z3 / MASK64) * 360
    
    # Trit fro