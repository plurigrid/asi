---
name: phase-portrait-generator
description: Generate phase portraits for 2D dynamical systems. Use when visualizing vector fields, nullclines, and trajectories.
version: 1.0.0
---


# Phase Portrait Generator

Generates phase portraits showing vector fields and trajectories in 2D state space.

## When to Use
- Visualizing 2D autonomous systems
- Plotting nullclines and equilibria
- Trajectory analysis in phase space

## GF(3) Role
PLUS (+1) Generator - creates visual outputs from differential equations.

## Quick Example

```python
import numpy as np
import matplotlib.pyplot as plt

def phase_portrait(f, xlim=(-3,3), ylim=(-3,3), density=20):
    x = np.linspace(*xlim, density)
    y = np.linspace(*ylim, density)
    X, Y = np.meshgrid(x, y)
    U, V = f(X, Y)
    plt.streamplot(X, Y, U, V, density=1.5)
    plt.xlabel('x'); plt.ylabel('y')

# Van der Pol oscillator
phase_portrait(lambda x, y: (y, -x + (1 - x**2) * y))
```

## Integration with bifurcation skills

Forms triad with:
- `bifurcation` (0): detects transitions
- `bifurcation-generator` (+1): parameter space
- `phase-portrait-generator` (+1): state space

## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 10. Adventure Game Example

**Concepts**: autonomous agent, game, synthesis

### GF(3) Balanced Triad

```
phase-portrait-generator (−) + SDF.Ch10 (+) + [balancer] (○) = 0
```

**Skill Trit**: -1 (MINUS - verification)

### Secondary Chapters

- Ch1: Flexibility through Abstraction

### Connection Pattern

Adventure games synthesize techniques. This skill integrates multiple patterns.
