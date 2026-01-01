# Triplet #2 Architecture: Modelica ⊗ Langevin-Dynamics ⊗ Fokker-Planck-Analyzer

## Overview

Triplet #2 enables **verification of chemical equilibrium** through three integrated computational streams:

- **MINUS (-1)**: Drift computation — Convert Modelica DAEs to Langevin SDEs
- **ERGODIC (0)**: Ensemble solving — Run stochastic simulations, extract distributions
- **PLUS (+1)**: Verification — Prove convergence to Gibbs equilibrium via Fokker-Planck analysis

## Problem Statement

**Question**: How do we prove that a chemical system reaches thermodynamic equilibrium?

**Challenge**: Direct measurement is slow; simulations accumulate numerical error; systems may be stiff or have multiple timescales.

**Solution**: Langevin-Fokker-Planck approach
1. Model reaction kinetics as a stochastic process (Langevin dynamics)
2. Solve ensemble of trajectories (accounts for thermal noise)
3. Verify convergence via Fokker-Planck equation (proves approach to Gibbs equilibrium)

## Data Flow

```
Modelica DAE
    ↓ (MINUS: modelica_to_langevin)
LangevinSDE struct
    ├─ drift: f(x,t)
    ├─ diffusion: g(x,t)
    ├─ noise_schedule: β(t) = 1/T(t)
    └─ metadata: reversibility, stiffness, etc.

    ↓ (ERGODIC: solve_langevin_ensemble)
Trajectories matrix (500 × dim × steps)

    ↓ (ERGODIC: extract_equilibrium_distribution)
EmpiricalDistribution
    ├─ mean: μ
    ├─ covariance: Σ
    └─ entropy: H

    ↓ (PLUS: compute_fokker_planck_check)
FokkerPlancVerification
    ├─ kl_divergence: D_KL(empirical || Gibbs)
    ├─ mixing_time: τ_mix (steps to convergence)
    ├─ is_reversible: detailed balance satisfied?
    └─ convergence_proof: human-readable certificate
```

## GF(3) Balance (Triplet Metrics)

Three metrics balanced via balanced ternary:

| Trit | Stream | Metric | Interpretation |
|------|--------|--------|-----------------|
| **MINUS (-1)** | Drift computation | ‖f(x)‖₂ | Energy dissipation rate |
| **ERGODIC (0)** | Ensemble sampling | dH/dt | Entropy production |
| **PLUS (+1)** | Verification | D_KL | Information gained from tests |

**Balance check**: All three metrics should be commensurate (within ~1.5× factor).

## Chemical Systems Handled

### 1. Reversible Reactions (A ⇌ B)
```
Example: A ⇌ B
k_f = 0.1 /s, k_r = 0.05 /s

Characteristics:
  - Detailed balance: YES
  - Stiff: NO
  - KL divergence threshold: < 0.05
  - Mixing time: < 100 steps
```

### 2. Irreversible Synthesis (A + B → C)
```
Example: Bimolecular synthesis
k = 0.1 /(M·s)

Characteristics:
  - Detailed balance: NO (absorbing boundary)
  - Stiff: Usually NO
  - KL divergence threshold: < 0.15 (harder to verify)
  - Mixing time: < 150 steps
```

### 3. Stiff Thermal Systems
```
Example: Kinetics + Heat equation
Reaction: exothermic (ΔH = -50 kJ/mol)
Heat dissipation: 10 W/K

Characteristics:
  - Multiple timescales (fast reaction, slow heat transfer)
  - Condition number: > 500
  - Stiff: YES (requires DASSL or Radau5)
  - KL divergence threshold: < 0.25
  - Mixing time: 100-250 steps
```

### 4. Enzyme Kinetics
```
Example: E + S ⇌ ES → E + P (Michaelis-Menten)
k_on = 0.5 /(M·s), k_off = 0.3 /s, k_cat = 0.1 /s

Characteristics:
  - Mixed reversibility (ES ⇌ E+S reversible, ES → P not)
  - Stiff: YES (fast + slow)
  - Quasi-steady-state approximation valid
  - KL divergence threshold: < 0.08
```

## Five-Layer Verification

### Layer 1: KL Divergence
**What**: Kullback-Leibler divergence from empirical to Gibbs distribution
**How**: D_KL = Σ p(x) log(p(x)/q(x))
**Threshold**: Depends on reversibility (0.05 reversible, 0.15 irreversible)

### Layer 2: Detailed Balance
**What**: Forward and backward transition rates equal at equilibrium
**How**: Check if P(x→y) * p(x) = P(y→x) * p(y)
**Indicator**: Should be true for reversible systems, false for irreversible

### Layer 3: Mixing Time
**What**: Number of steps to convergence
**How**: Estimate from spectral gap: τ_mix ≈ -1/log(λ₂)
**Target**: Fast mixing → system converges quickly to equilibrium

### Layer 4: Stiffness Detection
**What**: Condition number of drift Jacobian
**How**: cond(A) = λ_max / λ_min
**Interpretation**: cond > 1000 → use DASSL; cond > 100 → use implicit solver

### Layer 5: Conservation Law Validation
**What**: Mass, charge, and energy conservation
**How**: Check ∑ Δ(concentrations) = 0 over time
**Status**: Currently stubbed (future enhancement)

## API Reference

### MINUS Stream

```julia
sde = modelica_to_langevin(dae; temperature=300.0, damping=1.0)::LangevinSDE
```

Convert Modelica DAE to Langevin SDE.

**Inputs**:
- `dae::Dict`: Must contain `:equations`, `:parameters`, `:variables`
- `temperature::Float64`: Reaction temperature (K)
- `damping::Float64`: Friction coefficient in Langevin equation

**Returns**: `LangevinSDE` struct with drift, diffusion, and metadata

**Example**:
```julia
dae = Dict(
    :equations => ["d[A]/dt = -0.1*[A] + 0.05*[B]", "d[B]/dt = 0.1*[A] - 0.05*[B]"],
    :parameters => Dict("k_f" => 0.1, "k_r" => 0.05),
    :variables => ["[A]", "[B]"]
)
sde = modelica_to_langevin(dae; temperature=298.0)
```

### ERGODIC Stream

```julia
traj = solve_langevin_ensemble(sde, x0, T, dt, num_trajectories)::Trajectories
```

Solve ensemble of stochastic trajectories via Euler-Maruyama method.

**Inputs**:
- `sde::LangevinSDE`: System specification
- `x0::Vector`: Initial condition
- `T::Float64`: End time
- `dt::Float64`: Time step
- `num_trajectories::Int`: Number of parallel samples (typically 500)

**Returns**: `Trajectories` struct containing ensemble data

```julia
eq_dist = extract_equilibrium_distribution(trajectories; t_burnin=Int(0.3*n_steps))::EmpiricalDistribution
```

Extract steady-state distribution after burning in transient phase.

**Inputs**:
- `trajectories::Trajectories`: Full ensemble
- `t_burnin::Int`: Transient steps to skip

**Returns**: Mean, covariance, entropy of equilibrium distribution

### PLUS Stream

```julia
result = compute_fokker_planck_check(trajectories, sde)::FokkerPlancVerification
```

Five-layer verification of chemical equilibrium.

**Inputs**:
- `trajectories::Trajectories`: Ensemble data
- `sde::LangevinSDE`: System specification

**Returns**: `FokkerPlancVerification` with:
- `kl_divergence::Float64`: Convergence metric (< 0.05 excellent)
- `mixing_time_steps::Int`: Steps to equilibrium
- `is_reversible::Bool`: Detailed balance verified
- `condition_number::Float64`: Stiffness measure
- `convergence_proof::String`: Human-readable certificate
- `warnings::Vector{String}`: Issues detected
- `recommendations::Vector{String}`: Solver suggestions

**High-Level Entry Point**:

```julia
result = verify_chemical_equilibrium_via_langevin(
    dae;
    num_trials=100,
    temperature=300.0,
    output_path="report.json"
)::FokkerPlancVerification
```

Complete pipeline: Problem → Verification → JSON report

## Failure Diagnostics

### Convergence Fails (KL > threshold)

**Possible causes**:
1. **Stiff system**: condition number > 500
   - **Fix**: Use DASSL or Radau5 solver

2. **Irreversibility**: System has absorbing boundaries
   - **Fix**: Ensure k_r = 0 is intentional; monitor absorbing states

3. **Simulation too short**: Need T > 2τ_mix
   - **Fix**: Increase end time T

4. **Poor initial condition**: x₀ far from equilibrium
   - **Fix**: Choose x₀ near expected equilibrium

### Detailed Balance Violated

**Interpretation**: System is effectively irreversible; forward ≠ backward rates

**Action**: This is normal for irreversible reactions. Use loosened KL threshold (0.15 instead of 0.05).

### High Condition Number

**Interpretation**: Stiffness detected; solver must use implicit stepping

**Recommendation**: Use DASSL, Radau5, or other stiff integrator

## Integration with Other Skills

### Triplet #1 (Thermo-Game Synthesis)
Triplet #2 provides thermodynamic verification layer:
- Games propose multi-agent synthesis protocols
- Triplet #2 proves protocols reach equilibrium
- Conflict detector flags infeasible protocols

### Langevin-Dynamics Skill
Provides SDE solving and noise calibration:
- Can use more sophisticated integrators (not just Euler-Maruyama)
- Handles complex stochastic processes

### Fokker-Planck-Analyzer Skill
Provides advanced equilibrium analysis:
- Detailed balance checking
- Spectral gap computation
- Convergence rate estimation

## Performance Characteristics

| System Type | Typical Condition # | Mixing Time | KL Threshold | Solver |
|-------------|-------------------|-------------|--------------|--------|
| Reversible | 10-50 | 10-100 steps | < 0.05 | Euler-Maruyama |
| Irreversible | 20-100 | 50-150 steps | < 0.15 | Euler-Maruyama |
| Stiff thermal | 500-2000 | 100-250 steps | < 0.25 | DASSL |
| Enzyme | 200-800 | 80-200 steps | < 0.08 | Radau5 |

## References

- Langevin dynamics: Allen & Tildesley, *Computer Simulation of Liquids*
- Fokker-Planck equation: Risken, *The Fokker-Planck Equation*
- Detailed balance: Evans & Searles, *Transient fluctuation theorems*
- Stiff ODE solvers: Hairer & Wanner, *Solving Ordinary Differential Equations II*
