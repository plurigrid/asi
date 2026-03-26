---
name: nonlinear-dynamics-observatory
<<<<<<< HEAD
description: Unified observatory for learning in, on, and from nonlinear dynamical systems. Integrates dysts (attractor corpus), lolita (latent diffusion physics emulation), bayesian-breathing (Bayesian state estimation), geomstats (Riemannian manifold geometry), neuraloperator (FNO/DeepONet), panda (Patched Attention), hoi (higher-order interactions), and ontology's autopoietic ergodicity as the meta-theory.
version: 1.0.0
trit: 0
role: BRIDGE
tags: [dynamical-systems, attractors, lolita, physics-emulation, riemannian, neural-operator, bayesian, hoi, autopoiesis, gf3, interleave]
deployed: 2026-02-19
=======
description: >
  Unified observatory for learning in, on, and from nonlinear dynamical systems.
  Integrates dysts (attractor corpus), lolita (latent diffusion physics emulation),
  bayesian-breathing (Bayesian state estimation), geomstats (Riemannian manifold
  geometry), neuraloperator (FNO/DeepONet), panda (Patched Attention), and hoi
  (higher-order interactions). Use when working with strange attractors, physics
  emulation, attractor identification, or Riemannian geometry of dynamical systems.
>>>>>>> origin/main
---

# Nonlinear Dynamics Observatory

<<<<<<< HEAD
**Topos Story #23**: "every attractor is a sheaf section; learning = finding the natural transformation between systems"

## Component Map

```
dysts                    ← corpus of 130+ strange attractors
  ↓
panda                    ← Patched Attention for Nonlinear Dynamics (transformer patches)
  ↓
geomstats                ← Riemannian geometry of attractor basins (Fisher-Rao, geodesics)
  ↓
neuraloperator           ← FNO/DeepONet for infinite-dimensional operators
  ↓
lolita (arxiv:2507.02608)← latent diffusion physics emulation (1000x compression)
  ↓
bayesian-breathing       ← Bayesian state estimation (MCMC/SMC posterior over trajectory)
  ↓
hoi                      ← higher-order interactions (n-body dynamical couplings)
  ↓
ontology                 ← autopoietic ergodicity as meta-theory (attractor = identity)
```

## GF(3) Tripartite Tag

`dysts(-1) ⊗ nonlinear-dynamics-observatory(0) ⊗ lolita(+1) = 0`

Validation (-1, ground truth corpus) × Bridge (0, routing) × Generation (+1, emulation) = 0.

---

## The Core Vision

Every **attractor** in `dysts` is a **sheaf section**: a locally consistent assignment of state to each time-point, globally stitched by the dynamical law. **Learning** a dynamical system = finding the **natural transformation** between two sheaves (the ground-truth attractor sheaf and the learned model sheaf).

`lolita` emulates this at 1000× compression via latent diffusion. `bayesian-breathing` maintains a probabilistic posterior over which attractor family generated the observed trajectory. `geomstats` measures distances between attractor basins on the Riemannian manifold of probability distributions. `ontology`'s autopoietic ergodicity provides the thermodynamic grounding: a stable attractor IS an autopoietically ergodic state.

---

## 1. dysts — Strange Attractor Corpus
=======
## Component Map

```
dysts                    <- corpus of 130+ strange attractors
  |
panda                    <- Patched Attention for Nonlinear Dynamics (transformer patches)
  |
geomstats                <- Riemannian geometry of attractor basins (Fisher-Rao, geodesics)
  |
neuraloperator           <- FNO/DeepONet for infinite-dimensional operators
  |
lolita (arxiv:2507.02608)<- latent diffusion physics emulation (1000x compression)
  |
bayesian-breathing       <- Bayesian state estimation (MCMC/SMC posterior over trajectory)
  |
hoi                      <- higher-order interactions (n-body dynamical couplings)
```

## 1. dysts -- Strange Attractor Corpus
>>>>>>> origin/main

```python
import dysts.flows as flows
from dysts.datasets import load_file

<<<<<<< HEAD
# Load attractor by name
=======
>>>>>>> origin/main
lorenz = flows.Lorenz()
traj = lorenz.make_trajectory(n=10000, pts_per_period=50)
# traj.shape = (10000, 3)

<<<<<<< HEAD
# All attractors with metadata
from dysts import get_attractor_list
attractors = get_attractor_list()  # 130+ named attractors

# GF(3) classification by Lyapunov spectrum
def classify_trit(attractor):
    """Classify attractor by first Lyapunov exponent."""
    λ = attractor.lyapunov_exponent()
    if λ > 0: return +1   # chaotic (Generator)
    if λ < 0: return -1   # stable fixed point (Validator)
    return 0              # marginal / limit cycle (Coordinator)
```

---

## 2. lolita — Latent Diffusion Physics Emulation

(NeurIPS 2025, arxiv:2507.02608): DCAE autoencoder (lat_channels=64) + ViT diffusion on latents.
=======
from dysts import get_attractor_list
attractors = get_attractor_list()  # 130+ named attractors

def classify_by_lyapunov(attractor):
    """Classify attractor by first Lyapunov exponent."""
    lam = attractor.lyapunov_exponent()
    if lam > 0: return +1   # chaotic
    if lam < 0: return -1   # stable fixed point
    return 0                # marginal / limit cycle
```

## 2. lolita -- Latent Diffusion Physics Emulation

NeurIPS 2025 (arxiv:2507.02608): DCAE autoencoder (lat_channels=64) + ViT diffusion on latents.
>>>>>>> origin/main

```python
from lolita import LolitaEmulator

<<<<<<< HEAD
# Train on dysts corpus
emulator = LolitaEmulator(lat_channels=64, dataset="rayleigh_benard")
emulator.train(epochs=100, batch_size=32)

# Generate novel physics trajectory
new_trajectory = emulator.sample(
    initial_condition=lorenz.ic,
    n_steps=1000,
    guidance_scale=7.5  # classifier-free guidance
)

# Evaluate: is the emulated trajectory on the correct attractor?
=======
emulator = LolitaEmulator(lat_channels=64, dataset="rayleigh_benard")
emulator.train(epochs=100, batch_size=32)

new_trajectory = emulator.sample(
    initial_condition=lorenz.ic,
    n_steps=1000,
    guidance_scale=7.5
)

>>>>>>> origin/main
from lolita.eval import rollout_error
err = rollout_error(new_trajectory, lorenz.make_trajectory(1000))
# Good emulation: err < 0.05
```

<<<<<<< HEAD
**Datasets**: Euler equations, Rayleigh-Bénard convection, Turbulence Gravity Cooling (from The Well).

---

## 3. panda — Patched Attention for Nonlinear Dynamics

Transformer with patches over attractor phase space:
=======
Datasets: Euler equations, Rayleigh-Benard convection, Turbulence Gravity Cooling (from The Well).

## 3. panda -- Patched Attention for Nonlinear Dynamics
>>>>>>> origin/main

```python
from panda import PatchedAttentionModel

<<<<<<< HEAD
# Divide attractor trajectory into patches
model = PatchedAttentionModel(
    patch_size=50,        # time steps per patch
    d_model=256,
    n_heads=8,
    n_layers=6,
    attractor_dim=3       # dimensionality (e.g. Lorenz = 3D)
)

# Train: predict next patch from context patches
model.train(dysts_trajectories, epochs=50)

# Extrapolate: given 200 steps, predict 800 more
context = lorenz_traj[:200]
prediction = model.rollout(context, n_steps=800)
```

---

## 4. geomstats — Riemannian Geometry of Attractor Basins
=======
model = PatchedAttentionModel(
    patch_size=50,
    d_model=256,
    n_heads=8,
    n_layers=6,
    attractor_dim=3
)
model.train(dysts_trajectories, epochs=50)
prediction = model.rollout(lorenz_traj[:200], n_steps=800)
```

## 4. geomstats -- Riemannian Geometry of Attractor Basins
>>>>>>> origin/main

```python
import geomstats.backend as gs
from geomstats.geometry.spd_matrices import SPDMatrices
from geomstats.statistics.frechet_mean import FrechetMean

<<<<<<< HEAD
# Represent each attractor as a covariance matrix (SPD)
def attractor_covariance(traj):
    return gs.array(np.cov(traj.T))

# Fisher-Rao distance between attractors (on SPD manifold)
manifold = SPDMatrices(n=3)  # 3D attractors
lorenz_spd = attractor_covariance(lorenz_traj)
rossler_spd = attractor_covariance(rossler_traj)

distance = manifold.metric.dist(lorenz_spd, rossler_spd)
# Fisher-Rao distance = information-geometric separation of attractors

# Fréchet mean of attractor family (centroid on manifold)
=======
def attractor_covariance(traj):
    return gs.array(np.cov(traj.T))

manifold = SPDMatrices(n=3)  # 3D attractors
distance = manifold.metric.dist(lorenz_spd, rossler_spd)

>>>>>>> origin/main
mean_calculator = FrechetMean(manifold.metric)
family_centroid = mean_calculator.fit([spd1, spd2, spd3]).estimate_
```

<<<<<<< HEAD
**Connection to BCI**: Fisher-Rao distance on SPD matrices is EXACTLY what `bci-phenomenology` uses for 8ch EEG covariance — the EEG manifold IS an attractor manifold.

---

## 5. neuraloperator — Infinite-Dimensional Function Operators
=======
Fisher-Rao distance on SPD matrices is the same metric used by bci-phenomenology for 8ch EEG covariance.

## 5. neuraloperator -- Infinite-Dimensional Function Operators
>>>>>>> origin/main

```python
from neuraloperator.models import FNO

<<<<<<< HEAD
# Fourier Neural Operator for PDE learning
fno = FNO(
    n_modes=(16, 16),      # Fourier modes
    hidden_channels=64,
    in_channels=1,          # initial condition
    out_channels=1,         # solution at time T
    n_layers=4,
)

# Train: learn the solution operator of Rayleigh-Bénard PDE
# input: initial temperature field → output: field at t=1.0
fno.train(rb_dataset, epochs=200)

# Evaluate at any resolution (operator != network)
hi_res_solution = fno(initial_condition_64x64)  # 64x64 resolution
lo_res_solution = fno(initial_condition_16x16)  # 16x16 resolution
```

**Connection to lolita**: lolita compresses PDE solutions via DCAE, then diffuses in latent space. FNO learns the solution operator directly. These are complementary: FNO for fast single-step, lolita for generative rollout.

---

## 6. bayesian-breathing — Bayesian State Estimation

```python
# Which attractor generated this observed trajectory?
# Posterior: P(attractor | observations) via monad-bayes SMC

import pymc as pm
import numpy as np
=======
fno = FNO(
    n_modes=(16, 16),
    hidden_channels=64,
    in_channels=1,
    out_channels=1,
    n_layers=4,
)
fno.train(rb_dataset, epochs=200)

# Evaluate at any resolution (operator != network)
hi_res = fno(initial_condition_64x64)
lo_res = fno(initial_condition_16x16)
```

FNO learns the solution operator directly. Complementary to lolita: FNO for fast single-step, lolita for generative rollout.

## 6. bayesian-breathing -- Bayesian State Estimation

```python
import pymc as pm
>>>>>>> origin/main

def attractor_identification_model(observations):
    """Identify attractor family from noisy trajectory."""
    with pm.Model() as model:
<<<<<<< HEAD
        # Prior: uniform over attractor families
        attractor_idx = pm.Categorical("attractor", p=[1/130] * 130)

        # Likelihood: Riemannian distance to attractor covariance
        obs_cov = np.cov(observations.T)
        attractor_covs = [attractor_covariance(a) for a in ALL_ATTRACTORS]

        # Fisher-Rao distance as likelihood (via geomstats)
        dist = fisher_rao_distance(obs_cov, attractor_covs[attractor_idx])
        pm.Potential("likelihood", -dist**2 / (2 * 0.1**2))

        # Sample posterior
        trace = pm.sample(2000, tune=1000, cores=4)
    return trace

# RMSMC version (from monad-bayes)
# Sequential identification as new observations arrive
posterior = rmsmc_attractor_identification(streaming_traj)
```

---

## 7. hoi — Higher-Order Interactions

Beyond pairwise couplings in attractor networks:
=======
        attractor_idx = pm.Categorical("attractor", p=[1/130] * 130)
        obs_cov = np.cov(observations.T)
        dist = fisher_rao_distance(obs_cov, attractor_covs[attractor_idx])
        pm.Potential("likelihood", -dist**2 / (2 * 0.1**2))
        trace = pm.sample(2000, tune=1000, cores=4)
    return trace
```

## 7. hoi -- Higher-Order Interactions
>>>>>>> origin/main

```python
from hoi import Oinfo, HOI

<<<<<<< HEAD
# Measure n-body interactions in attractor state variables
hoi_analysis = HOI(method="oinfo")

# 3D Lorenz: which triplets of variables have synergistic HOI?
=======
hoi_analysis = HOI(method="oinfo")
>>>>>>> origin/main
lorenz_data = lorenz.make_trajectory(5000)
oinfo_values = hoi_analysis.fit(lorenz_data)
# oinfo > 0: redundancy (attractor dimension collapse)
# oinfo < 0: synergy (chaos amplification)
<<<<<<< HEAD

# Compare HOI across attractors
def hoi_fingerprint(attractor):
    traj = attractor.make_trajectory(5000)
    return hoi_analysis.fit(traj)
```

---

## 8. Autopoietic Ergodicity as Meta-Theory

From `plurigrid/ontology`: a stable attractor IS an autopoietically ergodic state.

```python
def is_autopoietically_ergodic(traj, epsilon=0.05):
    """Check if trajectory has stabilized to an ergodic attractor."""
    # Condition 1: time average ≈ ensemble average (ergodicity)
    time_avg = np.mean(traj, axis=0)
    ensemble_avg = np.mean([attractor.make_trajectory(100)[-1]
                             for _ in range(100)], axis=0)
    ergodic = np.linalg.norm(time_avg - ensemble_avg) < epsilon

    # Condition 2: Lyapunov stability (attractor is self-maintaining)
    lyapunov = compute_lyapunov(traj)
    autopoietic = lyapunov < 0.5  # bounded chaos = stable self-organization

    return ergodic and autopoietic

# Every attractor in dysts that passes this test is an "identity"
# in the ontology sense: a self-maintaining, thermodynamically stable structure
identities = [a for a in get_attractor_list() if is_autopoietically_ergodic(a.make_trajectory(10000))]
```

---

=======
```

>>>>>>> origin/main
## Cross-Component Wiring

```
dysts (corpus)
<<<<<<< HEAD
  │── panda (transformer extrapolation)
  │── geomstats (Riemannian distances between attractors)
  │── neuraloperator (FNO solution operators)
  │
  └── lolita (latent diffusion emulation)
        │── monad-bayes PMMH (parameter inference)
        │── Vertex AI Pipelines (scale to GCP)
        │
        └── bayesian-breathing (posterior over attractor family)
              │── geomstats Fisher-Rao likelihood
              │── hoi (higher-order interaction diagnostics)
              │
              └── ontology (autopoietic ergodicity test)
                    └── GF(3) trit: +1=chaotic, 0=marginal, -1=stable
```

## Related ASI Skills

- `dysts` / `attractor` / `chaotic-attractor` — attractor corpus and dynamics
- `lolita` — latent diffusion physics emulation
- `bayesian-breathing` — posterior state estimation
- `trajectory` / `periodic-orbit` / `repeller` — trajectory analysis
- `monad-bayes-asi-interleave` — PMMH for lolita parameter inference
- `vertex-ai-protein-interleave` — KFP pipeline patterns (reuse for physics)
- `catlab-asi-interleave` — AlgebraicDynamics.jl for ODE composition
- `ontology-asi-interleave` — autopoietic ergodicity meta-theory
- `bci-colored-operad` — Fisher-Rao on EEG = Fisher-Rao on attractors
- `gay-monte-carlo` — GF(3)-colored MCMC sampling over attractor families
- `abductive-monte-carlo` — which attractor generated these observations?
- `ergodicity` — the convergence criterion
- `lyapunov-function` / `lyapunov-stability` — stability analysis
- `bifurcation` / `bifurcation-generator` — attractor birth/death
- `waddington-landscape` — energy landscape = potential function of dynamics
- `invariant-measure` / `invariant-set` — ergodic theory foundation
- `attractor` / `stable-manifold` / `unstable-manifold` — manifold structure
=======
  |-- panda (transformer extrapolation)
  |-- geomstats (Riemannian distances between attractors)
  |-- neuraloperator (FNO solution operators)
  |
  +-- lolita (latent diffusion emulation)
        |-- monad-bayes PMMH (parameter inference)
        |-- Vertex AI Pipelines (scale to GCP)
        |
        +-- bayesian-breathing (posterior over attractor family)
              |-- geomstats Fisher-Rao likelihood
              |-- hoi (higher-order interaction diagnostics)
```
>>>>>>> origin/main
