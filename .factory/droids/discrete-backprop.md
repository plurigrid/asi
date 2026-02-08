---
name: discrete-backprop
description: Gradient-free optimization via discrete perturbations and trit-based learning
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Discrete Backprop Skill

**Status**: ✅ Production Ready
**Trit**: +1 (PLUS - generator/executor)
**Principle**: Learn without continuous gradients using {-1, 0, +1} perturbations

---

## Overview

**Discrete Backprop** enables gradient-free learning for:

1. **Non-differentiable functions**: Hash lookups, conditionals, discrete choices
2. **Quantized networks**: Binary/ternary neural networks
3. **Combinatorial optimization**: Where gradients don't exist
4. **GF(3) systems**: Native trit-based learning

## Core Algorithm

```
Discrete Gradient Estimation:
  
  For each parameter θ:
    1. Perturb: θ⁺ = θ + ε, θ⁻ = θ - ε
    2. Evaluate: L⁺ = Loss(θ⁺), L⁻ = Loss(θ⁻)
    3. Estimate: ∇θ ≈ sign(L⁺ - L⁻)  →  {-1, 0, +1}
    
  Trit Gradient:
    - If L⁺ > L⁻: move negative → trit = -1
    - If L⁺ < L⁻: move positive → trit = +1
    - If L⁺ ≈ L⁻: stay         → trit = 0
```

## Python Implementation

```python
import random
from typing import Callable, List, Tuple
from dataclasses import dataclass

@dataclass
class TritGradient:
    """Gradient represented as trit {-1, 0, +1}."""
    value: int
    confidence: float
    
    def __post_init__(self):
        assert self.value in {-1, 0, 1}

class DiscreteBackprop:
    """Gradient-free optimization using discrete perturbations."""
    
    def __init__(self, dims: int, epsilon: float = 1.0, threshold: float = 0.01):
        self.dims = dims
        self.epsilon = epsilon
        self.threshold = threshold
    
    def trit_gradient(
        self, 
        params: List[float], 
        loss_fn: Callable[[List[float]], float]
    ) -> List[TritGradient]:
        """
        Compute trit-valued gradient via finite differences.
        
        Returns list of TritGradient for each parameter.
        """
        base_loss = loss_fn(params)
        gradients = []
        
        for i in range(len(params)):
            # Positive perturbation
            params_plus = params.copy()
            params_plus[i] += self.epsilon