---
name: fokker-planck-analyzer
description: ' Layer 5: Convergence to Equilibrium Analysis'
model: inherit
tools: read-only
---

# fokker-planck-analyzer

> Layer 5: Convergence to Equilibrium Analysis

## bmorphism Contributions

> *"what would it mean to become the Fokker-Planck equation—identity as probability flow?"*
> — [bmorphism gist](https://gist.github.com/bmorphism/a02cc1d1431d4e8b847fdc6276bc3614)

**Philosophical Frame**: The Fokker-Planck equation describes how probability distributions evolve over time. bmorphism's question about "becoming" the equation points to the deep connection between identity and probability flow — the self as a dynamical system converging to equilibrium.

**Active Inference Connection**: Fokker-Planck dynamics underlie [Active Inference in String Diagrams](https://arxiv.org/abs/2308.00861) (Tull, Kleiner, Smithe) where free energy minimization drives probabilistic belief updates.

**Version**: 1.0.0
**Trit**: -1 (Validator - verifies steady state)
**Bundle**: analysis
**Status**: ✅ New (validates Fokker-Planck convergence)

---

## Overview

**Fokker-Planck Analyzer** verifies that neural network training via Langevin dynamics has reached equilibrium. It checks whether the empirical weight distribution matches the theoretical Gibbs distribution predicted by Fokker-Planck theory.

**Key Insight**: Training that stops before reaching mixing time (τ_mix) ends up in different regions of the loss landscape than continuous theory predicts. This skill detects that gap.

## The Fokker-Planck Equation

```
∂p/∂t = ∇·(∇L(θ)·p) + T∆p

Boundary condition: p(θ, 0) = p₀(θ) [initial distribution]
Steady state:      p∞(θ) ∝ exp(-L(θ)/T) [Gibbs distribution]
```

Where:
- `p(θ, t)` = probability density of parameter θ at time t
- `L(θ)` = loss function
- `T` = temperature (controls noise scale)
- `∆p` = Laplacian (diffusion operator)

## Core Concepts

### Gibbs Distribution

At equilibrium, weights follow a Boltzmann-like distribution:

```
p∞(θ) ∝ exp(-L(θ)/T)

Interpretation:
- Lower loss → higher probability
- Temperature T controls sharpness:
  - Low T: Sharp peaks 