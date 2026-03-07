---
name: nonlinear-dynamics-observatory
description: >
  Unified observatory for learning in, on, and from nonlinear dynamical systems.
  Integrates dysts (attractor corpus), lolita (latent diffusion physics emulation),
  bayesian-breathing (Bayesian state estimation), geomstats (Riemannian manifold
  geometry), neuraloperator (FNO/DeepONet), panda (Patched Attention), and hoi
  (higher-order interactions). Use when working with strange attractors, physics
  emulation, attractor identification, or Riemannian geometry of dynamical systems.
---

# Nonlinear Dynamics Observatory

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

```python
import dysts.flows as flows
from dysts.datasets import load_file

lorenz = flows.Lorenz()
traj = lorenz.make_trajectory(n=10000, pts_per_period=50)
# traj.shape = (10000, 3)

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

```python
from lolita import LolitaEmulator

emulator = LolitaEmulator(lat_channels=64, dataset="rayleigh_benard")
emulator.train(epochs=100, batch_size=32)

new_trajectory = emulator.sample(
    initial_condition=lorenz.ic,
    n_steps=1000,
    guidance_scale=7.5
)

from lolita.eval import rollout_error
err = rollout_error(new_trajectory, lorenz.make_trajectory(1000))
# Good emulation: err < 0.05
```

Datasets: Euler equations, Rayleigh-Benard convection, Turbulence Gravity Cooling (from The Well).

## 3. panda -- Patched Attention for Nonlinear Dynamics

```python
from panda import PatchedAttentionModel

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

```python
import geomstats.backend as gs
from geomstats.geometry.spd_matrices import SPDMatrices
from geomstats.statistics.frechet_mean import FrechetMean

def attractor_covariance(traj):
    return gs.array(np.cov(traj.T))

manifold = SPDMatrices(n=3)  # 3D attractors
distance = manifold.metric.dist(lorenz_spd, rossler_spd)

mean_calculator = FrechetMean(manifold.metric)
family_centroid = mean_calculator.fit([spd1, spd2, spd3]).estimate_
```

Fisher-Rao distance on SPD matrices is the same metric used by bci-phenomenology for 8ch EEG covariance.

## 5. neuraloperator -- Infinite-Dimensional Function Operators

```python
from neuraloperator.models import FNO

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

def attractor_identification_model(observations):
    """Identify attractor family from noisy trajectory."""
    with pm.Model() as model:
        attractor_idx = pm.Categorical("attractor", p=[1/130] * 130)
        obs_cov = np.cov(observations.T)
        dist = fisher_rao_distance(obs_cov, attractor_covs[attractor_idx])
        pm.Potential("likelihood", -dist**2 / (2 * 0.1**2))
        trace = pm.sample(2000, tune=1000, cores=4)
    return trace
```

## 7. hoi -- Higher-Order Interactions

```python
from hoi import Oinfo, HOI

hoi_analysis = HOI(method="oinfo")
lorenz_data = lorenz.make_trajectory(5000)
oinfo_values = hoi_analysis.fit(lorenz_data)
# oinfo > 0: redundancy (attractor dimension collapse)
# oinfo < 0: synergy (chaos amplification)
```

## Cross-Component Wiring

```
dysts (corpus)
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
