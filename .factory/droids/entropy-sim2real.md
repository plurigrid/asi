---
name: entropy-sim2real
description: Entropy-driven sim2real transfer. Uses maximum entropy RL, domain randomization, and information-theoretic bridging to close the reality gap.
model: inherit
tools: read-only
---

# Entropy-Driven Sim2Real Transfer

**Trit**: -1 (MINUS - analysis/verification)
**Color**: #E85B8E (Rose Pink)
**URI**: skill://entropy-sim2real#E85B8E

## Core Insight

**Entropy bridges the sim-real gap by:**

1. **Maximizing entropy in simulation** → Policy sees diverse conditions
2. **Minimizing entropy at deployment** → Uncertainty collapses to reality
3. **Information-theoretic alignment** → Match distributions, not parameters

```
                    SIMULATION                      REALITY
                    
    High Entropy ─────────────────────────────▶ Low Entropy
    
    H(params) = max     ══════════▶      H(params) ≈ 0
    H(π|s) = high       ══════════▶      H(π|s) = focused
    p(sim) = broad      ══════════▶      p(real) = delta
    
    ┌─────────────────┐                ┌─────────────────┐
    │  MANY POSSIBLE  │    BRIDGE     │   ONE ACTUAL    │
    │     WORLDS      │───────────────│     WORLD       │
    │   (superpos.)   │               │   (collapsed)   │
    └─────────────────┘                └─────────────────┘
```

## Three Entropy Mechanisms

### 1. Domain Randomization Entropy

Maximize entropy over simulation parameters:

```python
import jax
import jax.numpy as jnp
from typing import Dict

class EntropyMaximizingRandomizer:
    """Domain randomization that maximizes parameter entropy."""
    
    def __init__(self, param_ranges: Dict[str, tuple]):
        self.param_ranges = param_ranges
        
    def entropy(self, distribution: str = "uniform") -> float:
        """Compute entropy of parameter distributions."""
        H = 0.0
        for name, (low, high) in self.param_ranges.items():
            if distribution == "uniform":
                # H(Uniform) = log(b - a)
                H += jnp.log(high - low)
            elif distribution == "gaussian":
                # H(Gaussian) = 0.5 * log(2πeσ²)
                sigma = (high - low) / 4  # 95% within range
                H += 0.5 * jnp.log(2 * jnp.pi * jnp.e * sigma**2)
   