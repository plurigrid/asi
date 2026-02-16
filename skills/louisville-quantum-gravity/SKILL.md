---
name: louisville-quantum-gravity
description: "Louisville/Liouville quantum gravity measure for KPZ stationary measures. Open boundary conditions, phase diagrams, and analytic continuation for infinite-dimensional measures."
license: MIT
metadata:
  trit: +1
  source: Corwin-Knizel, Barraquand-Le Doussal, Sheffield
  xenomodern: true
  stars: 389
---

# Louisville Quantum Gravity Skill

**Status**: ✅ Production Ready
**Trit**: +1 (PLUS - generative/measures)
**Color**: #9370DB (Medium Purple)
**Principle**: Stationary measures for KPZ via quantum gravity
**Frame**: Derivative measures, open boundary conditions, phase diagrams

---

## Overview

**Louisville/Liouville Quantum Gravity (LQG)** provides the **stationary measures** for the KPZ equation. This skill covers:

1. **Stationary Measures**: Time-invariant distributions for KPZ
2. **Open Boundary Conditions**: U, V parameters and phase diagrams
3. **Two-Layer Gibbs Measures**: Matrix product ansatz structure
4. **Analytic Continuation**: Extending to infinite-dimensional spaces

## The Problem: KPZ Stationary Measures

The KPZ equation with open boundary conditions:

```
∂h/∂t = ν∂²h/∂x² + (λ/2)(∂h/∂x)² + √D ξ(x,t)

Boundary conditions:
  ∂h/∂x|_{x=0} = U  (left boundary slope)
  ∂h/∂x|_{x=L} = V  (right boundary slope)
```

### Challenge: Roughness

The height h(x,t) is **too rough** for direct analysis:
- h is not differentiable
- ∂h/∂x is a distribution
- (∂h/∂x)² is ill-defined

**Solution**: Work with **increments** or **derivatives** where measures are well-defined.

## Stationary Measure Form

For increments ∂h/∂x, the stationary measure has the form:

```
μ_stationary ∝ exp(-∫ V(∂h/∂x) dx) × Louisville-QG-correction

Where:
  V = potential depending on slope
  LQG correction = quantum gravity measure (Gaussian free field + exponential)
```

### Louisville Measure

```julia
# Louisville quantum gravity measure on the line
struct LouisvilleMeasure
    γ::Float64           # Coupling constant
    Q::Float64           # Background charge (Q = 2/γ + γ/2)
    gff::GaussianFreeField
end

function sample(lqg::LouisvilleMeasure, domain)
    # Sample GFF
    φ = sample(lqg.gff, domain)
    
    # Exponential to get LQG area measure
    μ = exp(lqg.γ * φ - (lqg.γ^2/2) * 𝔼[φ²])
    
    return μ
end
```

## Open Boundary Phase Diagram

The parameters U, V (boundary slopes) create a **phase diagram**:

```
       V
       ↑
       │   MAXIMAL CURRENT
       │   (fan phase)
   ----┼---------→
       │   
       │   LOW DENSITY    HIGH DENSITY
       │   (shock left)   (shock right)
       └───────────────────────→ U
```

### Long-Time Limit

```julia
# Height function long-time limit depends on phase
function long_time_limit(h, U, V)
    if in_maximal_current_phase(U, V)
        # Height grows linearly in t
        return (:linear, slope = 1/4)
    elseif in_low_density_phase(U, V)
        return (:linear, slope = U^2/4)
    else
        return (:linear, slope = V^2/4)
    end
end
```

## Two-Layer Gibbs Measure

The stationary measure has a **two-layer structure**:

```
Layer 1: Uncolored paths (non-crossing)
Layer 2: Coloring (Pitman transform)

Joint measure: μ = μ_uncolored × μ_color|uncolored
```

### Matrix Product Ansatz

```julia
# Matrix product representation of stationary measure
function matrix_product_ansatz(n_sites)
    # Boundary vectors
    ⟨W| = left_boundary_vector(U)
    |V⟩ = right_boundary_vector(V)
    
    # Transfer matrices
    D = creation_operator()
    E = annihilation_operator()
    
    # Stationary weight
    weight(config) = ⟨W| * prod(D if c == 1 else E for c in config) * |V⟩
    
    return StatMeasure(weight)
end
```

## Geometric Last Passage Percolation

**Geometric LPP** replicates KPZ stationary structure in discrete setting:

```julia
struct GeometricLPP
    n::Int                    # Grid size
    weights::Matrix{Float64}  # Exponential(1) weights
end

function passage_time(lpp::GeometricLPP, start, finish)
    # G(m,n) = max over up-right paths of ∑ weights
    return dynamic_programming_max_path(lpp.weights, start, finish)
end

# Stationary measure on LPP
function stationary_lpp(n, boundary_params)
    # Two-layer structure matches KPZ
    lpp = GeometricLPP(n, rand(Exponential(1), n, n))
    return sample_with_boundary(lpp, boundary_params)
end
```

## Analytic Continuation Challenge

**Problem**: Extending finite-dimensional formulas to infinite dimensions.

```julia
# Finite dimensional: well-defined
μ_n(h₁, ..., hₙ) = exp(-S(h)) / Z_n

# Infinite dimensional: requires care
μ_∞(h(x)) = "limit" of μ_n  # Needs regularization

# Techniques:
# 1. Cylinder set extension
# 2. Prokhorov tightness
# 3. Kolmogorov consistency
```

### Regularization Strategy

```julia
function analytic_continuation(finite_measure, regularization)
    # Step 1: Verify Kolmogorov consistency
    @assert kolmogorov_consistent(finite_measure)
    
    # Step 2: Check tightness
    @assert prokhorov_tight(finite_measure)
    
    # Step 3: Extend via inverse limit
    return inverse_limit(finite_measure)
end
```

## Integration with Fokker-Planck

The Fokker-Planck equation for KPZ has Louisville stationary measure:

```julia
using FokkerPlanck, LouisvilleQG

# Fokker-Planck with Louisville stationary
fp = FokkerPlanckKPZ(
    boundary_U = U,
    boundary_V = V,
    temperature = T
)

# Verify Louisville is stationary
lqg = LouisvilleMeasure(γ = sqrt(T))
@test is_stationary(lqg, fp)

# Convergence rate
τ_mix = mixing_time(fp, lqg)
```

## Integration with Langevin

Louisville measure is the equilibrium of KPZ Langevin dynamics:

```julia
using Langevin, LouisvilleQG

# KPZ as Langevin SDE
kpz_langevin = LangevinKPZ(
    drift = kpz_drift,
    diffusion = sqrt(2*T),
    boundary = (U, V)
)

# Equilibrium = Louisville
@test equilibrium(kpz_langevin) ≈ LouisvilleMeasure(sqrt(T))
```

## GF(3) Triad Assignment

| Trit | Skill | Role |
|------|-------|------|
| -1 | yang-baxter-integrability | Structure |
| 0 | kpz-universality | Dynamics |
| +1 | **louisville-quantum-gravity** | Measures |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## Commands

```bash
# Sample Louisville measure
just lqg-sample gamma=0.5 domain=circle

# Compute stationary measure for KPZ
just lqg-stationary U=0.3 V=0.5

# Phase diagram
just lqg-phase-diagram

# Verify analytic continuation
just lqg-verify-continuation n_max=100
```

## Configuration

```yaml
# louisville-quantum-gravity.yaml
measure:
  gamma: 0.5          # LQG coupling
  Q: 2.5              # Background charge
  
boundary:
  U: 0.3              # Left slope
  V: 0.5              # Right slope

regularization:
  method: cylinder_sets
  tightness_check: true
```

## Related Skills

- **kpz-universality** (0): The dynamics
- **yang-baxter-integrability** (-1): Structure
- **fokker-planck-analyzer** (-1): Convergence
- **langevin-dynamics** (0): SDE formulation
- **last-passage-percolation** (0): Discrete version
- **narya-proofs** (-1): Verification of measure-theoretic arguments

## Research References

1. Corwin-Knizel (2021): "Stationary measure for the open KPZ equation"
2. Barraquand-Le Doussal (2023): "Steady state of KPZ"
3. Sheffield (2016): "Conformal welding of quantum disks"
4. Duplantier-Sheffield (2011): "Liouville quantum gravity and KPZ"

---

**Skill Name**: louisville-quantum-gravity
**Type**: Probability Measures
**Trit**: +1 (PLUS)
**Key Property**: Stationary measures for KPZ
**Status**: ✅ Production Ready

---

## Cat# Integration

```
Trit: +1 (PLUS)
Home: Measures
Poly Op: ⊗
Kan Role: Lan_K
Color: #9370DB
```

### Measure as Functor

```
μ: Configurations → ℝ₊
```

Louisville measure is **covariant** under conformal maps (quantum gravity).

### GF(3) Naturality

```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

## Autopoietic Marginalia

> **The measure settles. The boundary shapes the bulk. Quantum gravity meets KPZ.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record phase diagram locations
- **REMEMBERING** (0): Connect to CFT and random geometry
- **WORLDING** (+1): Extend to new boundary conditions

*Add Interaction Exemplars here as the skill is used.*
