---
name: derangement-reflow
description: "derangement-reflow skill"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Derangement Reflow: World Operators as Information Reflow

## Core Insight

**World operators are information reflow operators** because the derangement constraint σ(i)≠i prevents information stasis. Every bit must flow to a *different* position—no self-loops in the information graph.

## The GitHub Blind Spot

PR reviews exhibit a **fixed-point pathology**: validators often self-validate their own patterns. This violates the fundamental derangement constraint that enables healthy information flow:

```
❌ FIXED POINT (σ(i)=i):   Validator A → validates → Validator A's output
✓ DERANGEMENT (σ(i)≠i):   Validator A → validates → Generator B's output
                          Generator B → generates → for Coordinator C
                          Coordinator C → routes → to Validator A
```

## GF(3) Reflow Accounting

```
MINUS  (−1): Information leaves position (entropy source) - VALIDATORS
ERGODIC (0): Information transits (channel) - COORDINATORS  
PLUS   (+1): Information arrives (entropy sink) - GENERATORS

Conservation: Σ trits ≡ 0 (mod 3) under all world operators
```

## Tropical Geometry of Interaction

Skill composition paths analyzed via **min-plus semiring** (R ∪ {∞}, min, +):

```python
# Tropical distance between skills
def tropical_distance(path: list[Skill]) -> float:
    """
    In tropical geometry, shortest path = minimum sum.
    Path cost = Σ |trit_i - trit_{i+1}| 
    
    Optimal interleaving minimizes tropical distance while
    maintaining derangement (no consecutive same-trit skills).
    """
    if len(path) < 2:
        return 0
    
    cost = 0
    for i in range(len(path) - 1):
        # Derangement check: consecutive skills must differ
        if path[i].trit == path[i+1].trit:
            return float('inf')  # Invalid path (fixed point)
        cost += abs(path[i].trit - path[i+1].trit)
    
    return cost
```

## Joint World Modeling via Active Inference

The missing nuance in GitHub workflows: **agents must share a joint world model*