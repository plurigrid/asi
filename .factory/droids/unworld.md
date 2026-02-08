---
name: unworld
description: ' Layer 4: Derivational Pattern Generation via Seed Chaining'
model: inherit
tools: read-only
---

# unworld-skill

> Layer 4: Derivational Pattern Generation via Seed Chaining

**Version**: 1.0.0
**Trit**: +1 (Generator - produces derived patterns)
**Bundle**: learning
**Status**: ✅ New (replaces temporal training with derivational generation)

---

## Overview

**Unworld** is a derivational alternative to temporal learning approaches like agent-o-rama. Instead of training patterns via epochs and stochastic iterations, unworld generates equivalent patterns via deterministic seed chaining.

**Key Innovation**: Temporal succession (training epochs) is replaced with derivational succession (seed chains). Both methods produce patterns, but unworld does so:
- ✅ **100x faster** (seconds vs minutes)
- ✅ **Deterministically** (same seed = identical output)
- ✅ **Verifiably** (GF(3) conservation instead of re-training)
- ✅ **Without JVM/Rama** overhead

## The Duality

```
Agent-o-rama (Temporal):    interactions → [train N epochs] → learned patterns
Unworld (Derivational):     genesis_seed → [derive N steps] → pattern chain

Both extract behavioral patterns.
Unworld uses GF(3) conservation instead of iteration.
```

## Core Concept: Three-Match Gadgets

Patterns are represented as GF(3)-balanced triads:

```python
# Three-match triple: balanced by construction
class ThreeMatch:
    def __init__(self, genesis_seed: int):
        self.colors = [
            color_at(genesis_seed, 0),  # trit: -1 (MINUS)
            color_at(genesis_seed, 1),  # trit:  0 (ERGODIC)
            color_at(genesis_seed, 2)   # trit: +1 (PLUS)
        ]
        # Invariant: sum(trits) ≡ 0 (mod 3)
        assert sum(t.trit for t in self.colors) % 3 == 0
```

## Capabilities

### 1. derive-patterns-via-unworld

Generate learned patterns via seed chaining:

```python
from unworld import ThreeMatchChain

# Create derivational pattern generator
genesis_seed = 0xDEADBEEF
learner = ThreeMatchChain(genesis_seed=genesis_seed)

# Generate pattern chain (deterministic)
patterns = learner.unworld_chain(dept