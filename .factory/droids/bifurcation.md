---
name: bifurcation
description: Hopf bifurcation detection for dynamical system state transitions with GF(3) phase portraits
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Bifurcation

**Detects and navigates bifurcation points in dynamical systems where qualitative behavior changes.**

**Trit**: 0 (ERGODIC - Coordinator between stable states)
**Color**: #9966FF (Purple - neutral zone bridging warm/cold)

---

## Core Concepts

### Bifurcation Types

| Type | Description | GF(3) Mapping |
|------|-------------|---------------|
| **Saddle-Node** | Two equilibria collide and annihilate | PLUS ↔ MINUS collision |
| **Hopf** | Equilibrium → limit cycle | ERGODIC spawns oscillation |
| **Pitchfork** | Symmetry-breaking | One ERGODIC → two ±PLUS/MINUS |
| **Transcritical** | Exchange of stability | PLUS ↔ MINUS swap roles |
| **Period-Doubling** | Route to chaos | Trit cascade: 0 → 1 → -1 → 0... |

---

## Hopf Bifurcation Detection

```python
import numpy as np
from scipy.linalg import eig

def detect_hopf(jacobian_fn, params, param_name, param_range):
    """
    Detect Hopf bifurcation by finding where eigenvalues cross imaginary axis.

    At Hopf bifurcation:
    - Pair of complex conjugate eigenvalues
    - Real part crosses zero
    - Imaginary part nonzero (oscillation frequency)
    """
    bifurcation_points = []

    for p in param_range:
        params[param_name] = p
        J = jacobian_fn(params)
        eigenvalues = eig(J)[0]

        # Find complex conjugate pairs
        for ev in eigenvalues:
            if np.abs(np.imag(ev)) > 1e-6:  # Has imaginary part
                if np.abs(np.real(ev)) < 1e-4:  # Real part near zero
                    bifurcation_points.append({
                        'param': p,
                        'eigenvalue': ev,
                        'frequency': np.abs(np.imag(ev)),
                        'type': 'hopf'
                    })

    return bifurcation_points
```

---

## GF(3) Phase Portrait

```python
def gf3_phase_portrait(system_fn, x_range, y_range, trit_classifier):
    """
    Generate phase portrait with GF(3) coloring.

    Each region colored by dominant behavior:
    - P