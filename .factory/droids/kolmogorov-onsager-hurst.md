---
name: kolmogorov-onsager-hurst
description: "Turbulence scaling theory: K41 energy cascade, Onsager's anomalous dissipation, and Hurst exponent for long-range dependence"
model: inherit
tools: read-only
---

# Kolmogorov-Onsager-Hurst Skill

> *"Big whirls have little whirls that feed on their velocity,*
> *and little whirls have lesser whirls and so on to viscosity."*
> — Lewis Fry Richardson (1922)

## Overview

This skill connects three foundational concepts in scaling theory:

| Contributor | Year | Key Insight |
|-------------|------|-------------|
| **Kolmogorov** | 1941 | E(k) ~ k^(-5/3) energy spectrum |
| **Onsager** | 1949 | Anomalous dissipation at Hölder h ≤ 1/3 |
| **Hurst** | 1951 | H exponent measures long-range dependence |

## The K41 Energy Cascade

Kolmogorov's 1941 theory (K41) describes turbulent flow:

```
Energy injection (large scales)
        ↓
    Inertial range: E(k) ~ ε^(2/3) k^(-5/3)
        ↓
Dissipation (viscous scales)

Where:
  k = wavenumber (inverse length scale)
  ε = energy dissipation rate
  E(k) = energy spectrum
```

### The -5/3 Law

```python
import numpy as np

def kolmogorov_spectrum(k, epsilon=1.0, C_K=1.5):
    """
    Kolmogorov energy spectrum E(k) = C_K * ε^(2/3) * k^(-5/3)

    Args:
        k: wavenumber array
        epsilon: energy dissipation rate
        C_K: Kolmogorov constant (~1.5)

    Returns:
        Energy spectrum E(k)
    """
    return C_K * (epsilon ** (2/3)) * (k ** (-5/3))
```

## Onsager's Conjecture (1949)

Lars Onsager conjectured that:

1. **Smooth solutions** (Hölder h > 1/3): Energy is conserved
2. **Rough solutions** (Hölder h ≤ 1/3): Energy can dissipate without viscosity

```
Hölder continuity: |v(x) - v(y)| ≤ C |x - y|^h

h > 1/3  →  Energy conserved (Euler equations)
h = 1/3  →  Critical threshold (K41 prediction)
h < 1/3  →  Anomalous dissipation possible
```

### The 2022-2024 Resolution

Onsager's conjecture was proven in stages:
- **Isett (2018)**: h < 1/3 allows dissipation
- **Buckmaster-De Lellis-Székelyhidi-Vicol (2022-2024)**: Sharp threshold h = 1/3

This work contributed to **Fields Medal** recognition.

## Hurst Exponent

The Hurst exponent H ∈ (0, 1) measures persistence in time