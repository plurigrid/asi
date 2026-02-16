---
name: critical-opalescence
description: "Critical opalescence at phase transitions: diverging correlation length, light scattering, and the visual signature of criticality in fluids, proteins, and complex systems"
version: 1.0.0
trit: 0
polarity: ERGODIC
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
        # Rayleigh regime
        return xi ** 3
    else:
        # Large fluctuations
        return xi ** 2 * structure_factor(q, xi)
```

## Connection to Onsager

Lars Onsager's **exact solution of the 2D Ising model (1944)** gave the first rigorous calculation of critical behavior:

```
Onsager's Results:
─────────────────
Critical temperature: k_B T_c / J = 2 / ln(1 + √2) ≈ 2.269

Specific heat: C ~ |T - T_c|^(-α)  with α = 0 (log divergence)
Magnetization: M ~ |T - T_c|^β    with β = 1/8
Susceptibility: χ ~ |T - T_c|^(-γ) with γ = 7/4
Correlation length: ξ ~ |T - T_c|^(-ν) with ν = 1

The 2D Ising model is EXACTLY SOLVABLE.
Opalescence would occur if we could "see" spin fluctuations.
```

## Connection to Kolmogorov-Onsager-Hurst

```
┌─────────────────────────────────────────────────────────────────────┐
│              CRITICALITY ACROSS DOMAINS                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  KOLMOGOROV        ONSAGER           HURST          OPALESCENCE    │
│  (Turbulence)      (Phase Trans)     (Memory)       (Scattering)   │
│  ─────────────     ─────────────     ──────────     ─────────────  │
│  E(k) ~ k^(-5/3)   ξ ~ |t|^(-ν)      H = 1/3        I ~ ξ^d        │
│  Scale-free        Divergence        Long-range     All wavelengths│
│  Inertial range    Critical point    Persistence    Milky white    │
│                                                                     │
│  ─────────────────── UNIFYING THEME ──────────────────────────────  │
│                                                                     │
│  SCALE INVARIANCE: No characteristic length/time at criticality    │
│  UNIVERSALITY: Same exponents for different systems                 │
│  FLUCTUATIONS: Correlations extend to all scales                    │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## Protein Folding Connection

Proteins exhibit critical-like behavior:

```python
def protein_scattering(concentration, T, T_fold, radius_gyration=3.0):
    """
    Light scattering from protein solutions near folding transition.

    Near T_fold:
      - Molten globule state
      - Large fluctuations
      - Increased scattering

    Aggregation (misfolding):
      - Amyloid formation
      - Massive scattering (visible turbidity)
      - Opalescence in diseased states
    """
    xi = correlation_length(T, T_fold, xi_0=radius_gyration, nu=0.5)

    # Concentration-dependent scattering
    # Zimm equation for polymers
    I = concentration * xi ** 2

    return I

class FoldingLandscape:
    """
    Energy landscape for protein folding.

    Funnel topology with roughness:
      - Native state at bottom (global minimum)
      - Kinetic traps (local minima)
      - Chaperones smooth the landscape
    """

    def __init__(self, roughness=0.3, funnel_depth=10.0):
        self.roughness = roughness  # Local trap depth
        self.funnel_depth = funnel_depth  # Global bias

    def energy(self, q):
        """
        Energy as function of folding coordinate q ∈ [0, 1].
        q = 0: unfolded
        q = 1: native
        """
        # Funnel: linear bias toward native
        funnel = -self.funnel_depth * q

        # Roughness: random traps
        traps = self.roughness * np.sin(20 * np.pi * q)

        return funnel + traps

    def folding_rate(self, T):
        """
        Kramers rate over roughened landscape.
        """
        # Effective barrier reduced by funnel
        barrier = self.roughness * self.funnel_depth ** 0.5
        return np.exp(-barrier / T)
```

## Opalescence Types

| Type | Cause | Scale | Example |
|------|-------|-------|---------|
| **Critical** | ξ → ∞ at T_c | All scales | CO₂ critical point |
| **Rayleigh** | Particles << λ | ~1-10 nm | Blue sky, colloids |
| **Mie** | Particles ~ λ | 100-1000 nm | Clouds, milk |
| **Tyndall** | Particles > λ | 1-10 μm | Fog, suspensions |

## Structural Color (No Pigment)

Opalescence is related to **structural coloration**:

```
Photonic crystals:
  - Periodic structure with spacing ~ λ
  - Bragg diffraction → color selection
  - Examples: opals, butterfly wings, peacock feathers

The color depends on GEOMETRY, not chemistry.
Same principle as critical opalescence: interference at specific scales.
```

## GF(3) Integration

```
Trit: 0 (ERGODIC/Coordinator)

Critical opalescence is the BRIDGE between:
  - Microscopic fluctuations (atomic/molecular)
  - Macroscopic observables (turbidity, color)

GF(3) Triads:
  kolmogorov-onsager-hurst (-1) ⊗ critical-opalescence (0) ⊗ protein-folding (+1) = 0 ✓
  bifurcation-generator (-1) ⊗ critical-opalescence (0) ⊗ phase-transition (+1) = 0 ✓
  structural-stability (-1) ⊗ critical-opalescence (0) ⊗ symmetry-breaking (+1) = 0 ✓
```

## Practical Applications

### 1. Detecting Phase Transitions

```python
def detect_critical_point(T_array, scattering_array):
    """
    Find T_c from scattering data.
    Maximum scattering ≈ critical point.
    """
    idx = np.argmax(scattering_array)
    T_c = T_array[idx]

    # Fit ξ ~ |T - T_c|^(-ν) to extract ν
    # ...

    return T_c
```

### 2. Protein Aggregation Monitoring

Early detection of amyloid formation via light scattering.

### 3. Quality Control

Colloid stability, emulsion breakdown, crystallization.

## References

1. Onsager, L. (1944). "Crystal statistics. I. A two-dimensional model with an order-disorder transition." Physical Review.
2. Stanley, H.E. (1971). *Introduction to Phase Transitions and Critical Phenomena*.
3. Ornstein, L.S. & Zernike, F. (1914). "Accidental deviations of density and opalescence at the critical point."
4. Anfinsen, C.B. (1973). "Principles that govern the folding of protein chains." Science.

## Invocation

```
/critical-opalescence
```

Analyze systems for critical behavior via scattering signatures.
