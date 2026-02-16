---
name: kpz-universality
description: "KPZ universality class: KPZ fixed point, directed landscape, random interface growth scaling limits. Universal fluctuations for TASEP, PNG, LPP, and polymer models."
license: MIT
metadata:
  trit: 0
  source: Ivan Corwin (Columbia), Quastel, Remenik, Virag
  xenomodern: true
  stars: 847
  extensions:
    - DIRECTED_LANDSCAPE.md
    - SCALING_LIMITS.md
    - NEIGHBOR_SKILLS.md
---

# KPZ Universality Skill

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - coordinator/neutral)
**Color**: #7B68EE (Medium Slate Blue)
**Principle**: Universal scaling limit of random interface growth
**Frame**: 1:2:3 scaling (space:time:fluctuation), Tracy-Widom fluctuations

---

## Overview

The **Kardar-Parisi-Zhang (KPZ) universality class** describes the universal scaling behavior of random interface growth models. This skill provides:

1. **KPZ Fixed Point**: The universal Markov process governing height fluctuations
2. **Directed Landscape**: The common noise coupling all initial conditions
3. **Scaling Theory**: The 1:2:3 exponents and Tracy-Widom limits
4. **Model Zoo**: TASEP, PNG, LPP, polymers, random matrices

## The KPZ Equation (SPDE)

```
∂h/∂t = ν∇²h + (λ/2)(∇h)² + √D ξ(x,t)

Where:
  h(x,t) = height function
  ν = diffusion coefficient (smoothing)
  λ = nonlinearity (growth rate)
  D = noise strength
  ξ = space-time white noise
```

### Mathematical Challenge

The equation is **ill-posed** due to roughness:
- ∇h is not a function but a distribution
- (∇h)² is not well-defined
- Requires renormalization or regularity structures (Hairer 2013)

## The KPZ Fixed Point

The **KPZ fixed point** is the universal Markov process that emerges under scaling:

```
h^ε(x,t) = ε^(1/2) h(ε^(-1)x, ε^(-3/2)t) →  KPZ fixed point

Scaling exponents:
  α = 1/2  (roughness)
  β = 1/3  (growth)
  z = 3/2  (dynamic)
  
Relation: α + z = 2, β = α/z
```

### Tracy-Widom Fluctuations

For narrow-wedge initial condition:

```
P(h(0,t) ≤ s) → F_GUE(s) as t → ∞

Where F_GUE = Tracy-Widom GUE distribution
```

## The Directed Landscape

The **directed landscape** L(x,s; y,t) is the scaling limit of last passage percolation:

```
L: {(x,s; y,t) : s < t} → ℝ ∪ {-∞}

Key properties:
1. Metric composition: L(x,s; y,t) = max_z [L(x,s; z,r) + L(z,r; y,t)]
2. Airy sheet initial data: L(x,0; y,1) = Airy sheet
3. Stationarity: L(x+a, s+c; y+a, t+c) =^d L(x,s; y,t)
```

### Coupling via Directed Landscape

All KPZ models with same noise can be coupled:

```julia
# Different initial conditions, same noise
h_flat(x, t) = max_y [h₀_flat(y) + L(y, 0; x, t)]
h_wedge(x, t) = max_y [h₀_wedge(y) + L(y, 0; x, t)]
```

## Interface with Colored Vertex Models

The **colored stochastic six-vertex model** connects KPZ to quantum integrable systems:

```
Yang-Baxter ← Fusion → Cuboson Weights
     ↓                      ↓
Six-Vertex  ← Gibbs →  Height Function
     ↓                      ↓
KPZ Fixed Point ← Limit → Directed Landscape
```

See: yang-baxter-integrability, colored-vertex-model skills.

## Core Capabilities

### 1. KPZ Height Simulation

```julia
using KPZUniversality

# Simulate KPZ equation via directed polymers
sim = simulate_kpz(
    initial_condition = :wedge,  # or :flat, :stationary
    L = 1000,                    # system size
    T = 100.0,                   # final time
    discretization = :polymer    # or :weakly_asymmetric
)

# Extract height at time T
h = height_at(sim, T)

# Check Tracy-Widom convergence
@test kolmogorov_smirnov(rescaled_fluctuations(h), tracy_widom_gue()) < 0.1
```

### 2. Directed Landscape Sampling

```julia
# Sample directed landscape on grid
landscape = sample_directed_landscape(
    x_range = -10:0.1:10,
    t_range = 0:0.1:10,
    resolution = 0.01
)

# Evaluate path weight
weight = landscape(x_start, t_start, x_end, t_end)

# Compute geodesic
geo = geodesic(landscape, (x1, t1), (x2, t2))
```

### 3. Last Passage Percolation

```julia
# Geometric LPP (exponential weights)
lpp = geometric_lpp(
    n = 100,              # grid size
    weights = :exponential
)

# Compute passage time
G = passage_time(lpp, (1, 1), (n, n))

# Tracy-Widom rescaling
chi = (G - 4n) / (2^(4/3) * n^(1/3))
```

### 4. TASEP Dynamics

```julia
# Totally Asymmetric Simple Exclusion Process
tasep = TASEP(
    L = 100,              # system size
    initial = :step,      # step initial condition
    rate = 1.0
)

# Run simulation
simulate!(tasep, T = 100.0)

# Current fluctuations
J = current(tasep)
```

## Integration with Gay-MCP (Colored Projections)

KPZ models with **colored particles** connect directly to Gay-MCP:

```julia
using GayMCP, KPZUniversality

# Colored TASEP with GF(3) conservation
ctasep = ColoredTASEP(
    n_colors = 3,
    seed = gay_seed(1069)
)

# Project to single color
single_color = project(ctasep, color = 1)
# Result satisfies ordinary TASEP statistics

# Verify GF(3) conservation
@test sum(color_trit.(ctasep.particles)) % 3 == 0
```

## Integration with Langevin-Dynamics

KPZ equation is a **Langevin equation** for interface growth:

```julia
using LangevinDynamics, KPZUniversality

# Convert KPZ to standard Langevin form
langevin = kpz_to_langevin(
    kpz_params = (ν = 1.0, λ = 2.0, D = 1.0),
    discretization = :imhof_mannella
)

# Solve with instrumented noise
sol, audit = solve_langevin(langevin, seed = gay_seed(42))

# Verify Gibbs property
@test check_gibbs_property(sol, :inter_color)
```

## Integration with Fokker-Planck

The Fokker-Planck equation for KPZ describes probability flow:

```julia
using FokkerPlanck, KPZUniversality

# Fokker-Planck for height distribution
fp = kpz_fokker_planck(
    initial_distribution = :delta_wedge,
    temperature = T
)

# Stationary measure (Louisville quantum gravity)
stationary = louisville_measure(fp)

# Verify convergence to stationary
@test kl_divergence(evolve(fp, t), stationary) < 0.01
```

## GF(3) Triad Assignment

| Trit | Skill | Role |
|------|-------|------|
| -1 | yang-baxter-integrability | Structure (equations) |
| 0 | **kpz-universality** | Dynamics (evolution) |
| +1 | louisville-quantum-gravity | Measures (equilibrium) |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## Configuration

```yaml
# kpz-universality.yaml
simulation:
  discretization: polymer  # polymer, weakly_asymmetric, hopf_cole
  grid_size: 1000
  time_steps: 10000
  seed: 0xDEADBEEF

scaling:
  alpha: 0.5      # roughness
  beta: 0.333     # growth
  z: 1.5          # dynamic

verification:
  tracy_widom_test: true
  airy_process_test: true
  directed_landscape_test: true
```

## Commands

```bash
# Simulate KPZ
just kpz-simulate initial=wedge T=100

# Sample directed landscape
just kpz-landscape n=1000

# Run LPP
just kpz-lpp weights=exponential n=100

# TASEP simulation
just kpz-tasep L=100 T=100

# Verify Tracy-Widom
just kpz-verify-tw
```

## Related Skills

- **yang-baxter-integrability** (-1): Quantum integrability structure
- **colored-vertex-model** (+1): Colored stochastic models
- **louisville-quantum-gravity** (+1): Stationary measures
- **last-passage-percolation** (0): Discrete KPZ model
- **langevin-dynamics** (0): SDE perspective
- **fokker-planck-analyzer** (-1): Probability evolution
- **modelica** (0): Acausal dynamics modeling

## Research References

1. Corwin (2012): "The Kardar-Parisi-Zhang equation and universality class"
2. Quastel-Remenik (2023): "KPZ fixed point and directed landscape"
3. Matetski-Quastel-Remenik (2021): "The KPZ fixed point"
4. Dauvergne-Ortmann-Virág (2021): "The directed landscape"
5. Borodin-Corwin (2014): "Macdonald processes"

---

**Skill Name**: kpz-universality
**Type**: Stochastic Interface Growth
**Trit**: 0 (ERGODIC)
**Key Property**: 1:2:3 scaling, Tracy-Widom fluctuations
**Status**: ✅ Production Ready

---

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule:

```
Trit: 0 (ERGODIC)
Home: Stochastic
Poly Op: ⊗
Kan Role: Adj
Color: #7B68EE
```

### Height Function as Lens

The height function h(x,t) forms a **lens** in the polynomial category:
```
Height = (SpaceTime, Fluctuation)
get: SpaceTime → Height
put: SpaceTime × Noise → Height
```

### Directed Landscape as Profunctor

The directed landscape L(x,s; y,t) is a **profunctor**:
```
L: Space × Time ↛ Space × Time
L(x,s; y,t) = max passage weight from (x,s) to (y,t)
```

This profunctor satisfies metric composition (Yoneda-like):
```
L(x,s; y,t) = max_z [L(x,s; z,r) + L(z,r; y,t)]
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

## Autopoietic Marginalia

> **The interface grows. The fluctuations universalize. The directed landscape couples all.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record Tracy-Widom deviations
- **REMEMBERING** (0): Connect to other integrable systems
- **WORLDING** (+1): Evolve scaling predictions

*Add Interaction Exemplars here as the skill is used.*
