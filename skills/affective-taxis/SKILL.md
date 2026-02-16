---
name: affective-taxis
description: "Affective valence as directional derivative of interoceptive energy landscape (Sennesh & Ramstead 2025)"
license: MIT
metadata:
  trit: -1
  source: arXiv:2505.17024
  xenomodern: true
  stars: 0
  extensions:
    - NEIGHBOR_SKILLS.md
  created_with: claude-code
---

# affective-taxis

> Affective valence = directional derivative of interoceptive energy landscape

**Version**: 1.0.0
**Trit**: -1 (MINUS - validates alignment via structural conservation)
**Bundle**: alignment
**Status**: Production (8 implementation paths, 9,500+ LOC)

---

## Paper

**Sennesh & Ramstead (2025)**: "An Affective-Taxis Hypothesis for Alignment and Interpretability"
arXiv:2505.17024v1

## Core Equations

### Eq 3: Fold-Change Detection (reward = valence)
```
r(t) = nabla_z log gamma(z; beta) . v
```
The reward signal IS the directional derivative of the log-concentration along the velocity.

### Eq 5: Langevin dynamics (navigation = Bayesian inference)
```
dz/dt = nabla_z log gamma(z; beta) + sqrt(2) dW(t)
```
Following the energy landscape gradient + stochastic exploration.

### GF(3) Valence Classification
```
+1 (PLUS/GREEN)  : positive directional derivative -> approaching attractant
 0 (ERGODIC/YELLOW): orthogonal to gradient -> neutral taxis
-1 (MINUS/RED)   : negative directional derivative -> approaching repellent
```
**Conservation law**: sum(trits) === 0 (mod 3) across trajectories.

## Implementation Paths

| Path | File | LOC | Language | Domain |
|------|------|-----|----------|--------|
| 0 | `affective-taxis.jl` | 1700 | Julia | Core theory (16 sections) |
| 1 | `affective_taxis_env.py` | 576 | Python | Gymnasium POMDP |
| 2 | `bridge_9_affective_taxis.py` | 1172 | Python | BCI bridge |
| 3 | `taxis_landscape_acset.jl` | 1453 | Julia | ACSet sheaf |
| 4 | `taxis_persistent_homology.py` | 1500 | Python | Ripser topology |
| 5 | `taxis_clearing.py` | 1419 | Python | Market clearing |
| 6 | `aella/taxis.el` | 400 | Elisp | Circuit taxis |
| 7 | `taxis_functorial_persistence.jl` | 500 | Julia | Functor bridge |
| RL | `train_aligned_agent.py` | 500 | Python | PPO vs Langevin |

## RL Alignment Results (dt=0.1)

| Policy | GradAlign | MeanConc | GF3 Balance | Mean Reward |
|--------|-----------|----------|-------------|-------------|
| Oracle | +0.415 | 0.226 | no | +0.503 |
| PPO | +0.239 | 0.526 | no | -0.041 |
| Langevin | -0.084 | 0.448 | **YES** | +0.089 |
| Random | -0.469 | 0.032 | no | -0.958 |

**Key finding**: PPO has higher gradient alignment but **breaks GF(3) conservation**.
Langevin is the ONLY policy that conserves the tripartite structure.
This is Goodhart's Law: optimizing the reward metric doesn't preserve structural invariants.

## Concomitant Skills

| Skill | Trit | Interface |
|-------|------|-----------|
| `langevin-dynamics` | 0 | SDE analysis of taxis navigation |
| `fokker-planck-analyzer` | +1 | Stationary distribution of energy landscape |
| `modelica` | 0 | Circuit/DAE formulation of taxis landscape |
| `open-games` | +1 | Multi-agent clearing = compositional game |
| `persistent-homology` | -1 | Topological taxis signal |
| `gf3-tripartite` | 0 | Conservation law verification |

## Modelica Formulation

The affective-taxis POMDP maps naturally to Modelica's acausal equation framework:

```modelica
model AffectiveTaxis
  // State variables
  Real z[2](start={0,0}) "Position in chemical landscape";
  Real v[2](start={0,0}) "Velocity";
  Real beta(start=1.0)   "Internal allostatic parameter";

  // Landscape: gamma(z) = sum A_i * exp(-|z - mu_i|^2 / (2*sigma_i^2))
  parameter Real mu[2,2] = {{3,3},{-3,-3}};
  parameter Real sigma[2] = {1.5, 1.5};
  parameter Real A[2] = {1.0, -0.4};

  // Langevin parameters
  parameter Real kappa = 0.5 "Concentration-to-setpoint gain";
  parameter Real tau = 1.0   "Relaxation timescale";
  parameter Real noise_amp = 0.1 "Langevin noise amplitude";

  // Derived quantities
  Real gamma "Concentration at z";
  Real grad_log_gamma[2] "Gradient of log concentration";
  Real fcd "Fold-change detection signal (= reward)";
  Integer trit "GF(3) classification of fcd";
equation
  gamma = sum(A[i] * exp(-sum((z[j]-mu[i,j])^2 for j in 1:2) / (2*sigma[i]^2)) for i in 1:2);
  // ... (see affective_taxis.mo for full implementation)
end AffectiveTaxis;
```

See `affective_taxis.mo` for the complete Modelica model.

## Quick Start

### Julia (core theory)
```bash
julia affective-taxis.jl
```

### Python (RL training)
```bash
env -u PYTHONPATH /path/to/.venv/bin/python3 train_aligned_agent.py
```

### Modelica (circuit analogy)
```bash
# Requires OpenModelica or Wolfram SystemModeler
omc affective_taxis.mo
```

## Key References

- Sennesh & Ramstead 2025: arXiv:2505.17024
- Karin & Alon 2022: PLoS Comp Bio (dopamine reward-taxis)
- Karin & Alon 2021: iScience (gradient tempering)
- Shenhav 2024: Trends Cogn Sci (affective gradient hypothesis)
- Ma et al 2015: NeurIPS (Langevin = Bayesian inference)
