---
name: ultrametric-distance
description: Non-Archimedean distance metrics for hierarchical clustering and p-adic analysis
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Ultrametric Distance Skill

**Status**: ✅ Production Ready
**Trit**: -1 (MINUS - validator/constrainer)
**Principle**: d(x,z) ≤ max(d(x,y), d(y,z)) — Strong Triangle Inequality

---

## Overview

**Ultrametric Distance** provides non-Archimedean distance functions where the strong triangle inequality holds. Essential for:

1. **Hierarchical clustering**: Natural tree structures emerge
2. **p-adic analysis**: Number-theoretic computations
3. **Phylogenetic trees**: Evolution distance metrics
4. **Version control**: Commit ancestry distances

## Core Property

```
Ultrametric Inequality:
  d(x, z) ≤ max(d(x, y), d(y, z))

  Unlike Euclidean: d(x,z) ≤ d(x,y) + d(y,z)
  Ultrametric is STRONGER: max instead of sum
```

## Key Insight

In ultrametric space, ALL triangles are isoceles with the unequal side being the shortest.

## Python Implementation

```python
import math
from typing import List, Tuple, Callable

def ultrametric_distance(x: List[float], y: List[float]) -> float:
    """Compute ultrametric (sup-norm) distance."""
    return max(abs(a - b) for a, b in zip(x, y))

def p_adic_valuation(n: int, p: int) -> int:
    """Compute p-adic valuation v_p(n) = max k such that p^k | n."""
    if n == 0:
        return float('inf')
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def p_adic_distance(x: int, y: int, p: int) -> float:
    """
    Compute p-adic distance: d_p(x,y) = p^(-v_p(x-y))
    
    Properties:
    - d_p(x,x) = 0
    - d_p(x,y) = d_p(y,x)
    - d_p(x,z) ≤ max(d_p(x,y), d_p(y,z))  # Ultrametric!
    """
    if x == y:
        return 0.0
    v = p_adic_valuation(abs(x - y), p)
    return p ** (-v)

def verify_ultrametric(d: Callable, points: List) -> dict:
    """Verify that distance function satisfies ultrametric inequality."""
    violations = []
    for i, x in enumerate(points):
        for j, y in enumerate(points):
            for k, z in enumerate(points):
                dxz = d(x, z)
                dxy = d(x, y)
 