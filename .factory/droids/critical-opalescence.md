---
name: critical-opalescence
description: "Critical opalescence at phase transitions: diverging correlation length, light scattering, and the visual signature of criticality in fluids, proteins, and complex systems"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Critical Opalescence Skill

> *"At the critical point, the fluid becomes opalescent—milky white—because density fluctuations occur at all scales, scattering light of all wavelengths."*

## Overview

**Critical opalescence** is the dramatic increase in light scattering near a phase transition's critical point. It's the *visual signature of criticality*.

| System | Critical Point | Observable |
|--------|----------------|------------|
| CO₂ | 31°C, 73 atm | Milky fluid |
| Binary mixtures | Consolute point | Turbidity divergence |
| Proteins | Folding transition | Aggregate scattering |
| Ising model | T_c (Onsager: 2D exact) | Correlation length → ∞ |

## The Physics

### Why Opalescence at Criticality?

```
Normal state:
  ξ (correlation length) ~ 1 nm
  Fluctuations small, invisible

Near critical point:
  ξ → ∞ (diverges)
  Fluctuations at ALL scales
  λ_light ~ ξ → strong scattering

At T_c:
  ξ = ∞
  Scale-free fluctuations
  Maximum opalescence
```

### Ornstein-Zernike Theory

```python
import numpy as np

def structure_factor(q, xi, chi_0=1.0):
    """
    Ornstein-Zernike structure factor S(q).

    S(q) = χ₀ / (1 + q²ξ²)

    Args:
        q: scattering wavevector
        xi: correlation length
        chi_0: susceptibility amplitude

    At criticality (ξ → ∞): S(q) ~ q^(-2)
    """
    return chi_0 / (1 + (q * xi) ** 2)

def correlation_length(T, T_c, xi_0=1.0, nu=0.63):
    """
    Correlation length divergence near T_c.

    ξ = ξ₀ |T - T_c|^(-ν)

    Args:
        T: temperature
        T_c: critical temperature
        xi_0: microscopic length
        nu: critical exponent (3D Ising: 0.63, mean field: 0.5)
    """
    t = abs(T - T_c) / T_c
    if t < 1e-10:
        return float('inf')
    return xi_0 * (t ** (-nu))

def scattering_intensity(wavelength, xi):
    """
    Rayleigh-Gans scattering intensity.

    I ~ ξ³ for ξ << λ
    I ~ ξ² for ξ >> λ (Porod regime)
    """
    q = 2 * np.pi / wavelength
    if xi < wavelength / 10:
        # Rayleig