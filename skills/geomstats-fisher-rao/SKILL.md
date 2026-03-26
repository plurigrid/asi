---
name: geomstats-fisher-rao
<<<<<<< HEAD
description: Information geometry for Bayesian inference. Fisher-Rao metric on statistical manifolds, Riemannian optimization for model selection, Wasserstein geodesics connecting geomstats to Gromov-Wasserstein optimal transport.
---

# geomstats-fisher-rao Skill

> *The natural metric on probability distributions is the Fisher-Rao metric*

## What It Covers
=======
description: >
  Information geometry for Bayesian inference via geomstats.
  Triggers: Fisher-Rao metric, statistical manifolds, Riemannian optimization,
  Wasserstein geodesics, Gromov-Wasserstein optimal transport,
  hyperbolic embeddings, SPD matrices.
---

# geomstats-fisher-rao

Information geometry connecting geomstats to Bayesian inference and optimal transport.

## Coverage
>>>>>>> origin/main

22 notebooks in plurigrid's geomstats fork spanning:
- Information geometry (Fisher information matrix as Riemannian metric)
- Hyperbolic embeddings (Poincare ball, hyperboloid)
- Graph space (Frechet mean of graphs)
- Heisenberg group geometry
- SPD matrices (covariance manifolds)

## monad-bayes Connection

<<<<<<< HEAD
The Fisher-Rao metric is the unique Riemannian metric (up to scale) that is
invariant under sufficient statistics. This means:

```
MonadDistribution m => FisherRao (distribution m)
```

Every `score`/`factor` call in monad-bayes implicitly moves along a geodesic
on the Fisher-Rao manifold. The MCMC acceptance ratio is the exponential map.
=======
The Fisher-Rao metric is the unique Riemannian metric (up to scale) invariant under sufficient statistics:
>>>>>>> origin/main

```haskell
-- Natural gradient MCMC on Fisher-Rao manifold
naturalGradientStep :: MonadMeasure m => SPDMatrix -> m Parameters
naturalGradientStep fisherInfo = do
  currentParams <- get
  proposal <- mvNormal currentParams (inverse fisherInfo)
  let logRatio = logLikelihood proposal - logLikelihood currentParams
  accept <- bernoulli (min 1 (exp logRatio))
  if accept then return proposal else return currentParams
```

<<<<<<< HEAD
## Gromov-Wasserstein Bridge

geomstats <-> plurigrid/ontology:GW via optimal transport:
- Wasserstein distance = geodesic distance on the space of measures
- Gromov-Wasserstein = comparison of metric measure spaces
- Entropic regularization = softmax (connects to monad-bayes softmax)
- Bregman projections for marginal constraints

## Applications
- Cortical manifold geometry (zubyul/Nikolova_lab)
- Protein structure manifolds (Vertex AI)
- Eye movement geometry on the visual sphere (zubyul/EyeGestures)
- Color gamut as Riemannian manifold (Gay.jl DeltaE2000)

## GF(3) Trit Classification
| Component | Trit | Role |
|-----------|------|------|
| geomstats computation | +1 | Generation (geometric objects) |
| Fisher-Rao metric | 0 | Coordination (natural metric) |
| Wasserstein validation | -1 | Validation (distance bounds) |

Conservation: +1 + 0 + (-1) = 0

## Trit: 0 (ERGODIC)
=======
Every `score`/`factor` call in monad-bayes implicitly moves along a geodesic on the Fisher-Rao manifold. The MCMC acceptance ratio is the exponential map.

## Gromov-Wasserstein Bridge

geomstats connects to Gromov-Wasserstein optimal transport:
- Wasserstein distance = geodesic distance on the space of measures
- Gromov-Wasserstein = comparison of metric measure spaces
- Entropic regularization = softmax (connects to monad-bayes)
- Bregman projections for marginal constraints

## Applications

- Cortical manifold geometry
- Protein structure manifolds (Vertex AI)
- Eye movement geometry on the visual sphere
- Color gamut as Riemannian manifold (DeltaE2000)

## Concrete Affordance: Runnable Fisher-Rao Distance Computation

### Install

```bash
pip install geomstats
# geomstats pulls in numpy, scipy, matplotlib
```

### Plurigrid Fork

```bash
# Clone the plurigrid fork (already present locally):
git clone git@github.com:plurigrid/geomstats.git

# Upstream:
# git clone git@github.com:geomstats/geomstats.git
```

**Local fork path**: `/Users/alice/v/worlds/g/geomstats`

### Notebooks (21 in the fork)

| # | Topic | Path |
|---|---|---|
| 00 | Introduction to geomstats | `notebooks/00_foundations__introduction_to_geomstats.ipynb` |
| 02 | Connection & Riemannian metric | `notebooks/02_foundations__connection_riemannian_metric.ipynb` |
| 08 | **Information geometry** (Fisher-Rao) | `notebooks/08_practical_methods__information_geometry.ipynb` |
| 12 | EMG classification on SPD manifold | `notebooks/12_real_world_applications__emg_sign_classification_in_spd_manifold.ipynb` |
| 13 | Graph embedding in hyperbolic space | `notebooks/13_real_world_applications__graph_embedding_and_clustering_in_hyperbolic_space.ipynb` |
| 20 | Graph space (Frechet mean) | `notebooks/20_real_world_applications__graph_space.ipynb` |
| 21 | Heisenberg group geometry | `notebooks/21_foundations__sub_riemannian_geometry_and_the_heisenberg_group.ipynb` |

All notebooks at: `/Users/alice/v/worlds/g/geomstats/notebooks/`

### Runnable: Fisher-Rao Distance Between Two Normal Distributions

```python
#!/usr/bin/env python3
"""
Compute Fisher-Rao geodesic distance between two univariate normal
distributions on the statistical manifold.

The Fisher information matrix for N(mu, sigma^2) is:
  g = diag(1/sigma^2, 2/sigma^2)

The Fisher-Rao distance between N(mu1,s1^2) and N(mu2,s2^2) is the
geodesic distance on the upper half-plane with this metric.

Run:
  python3 fisher_rao_demo.py
"""

import geomstats.backend as gs
gs.random.seed(42)

from geomstats.information_geometry.normal import NormalDistributions

# The statistical manifold of univariate normals
manifold = NormalDistributions()

# Two distributions: N(0, 1) and N(3, 2)
# Parameters are [mu, sigma] (NOT sigma^2)
p = gs.array([0.0, 1.0])   # N(0, 1)
q = gs.array([3.0, 2.0])   # N(3, 2)

# Fisher-Rao geodesic distance
dist = manifold.metric.dist(p, q)
print(f"Fisher-Rao distance between N(0,1) and N(3,2): {float(dist):.6f}")

# Geodesic curve (10 points from p to q on the statistical manifold)
geodesic_fn = manifold.metric.geodesic(initial_point=p, end_point=q)
t = gs.linspace(0.0, 1.0, 10)
geodesic_points = geodesic_fn(t)
print(f"\nGeodesic path (mu, sigma) from N(0,1) → N(3,2):")
for i, pt in enumerate(geodesic_points):
    print(f"  t={float(t[i]):.1f}: N({float(pt[0]):.3f}, {float(pt[1]):.3f})")

# Fisher information matrix at a point
fim = manifold.metric.metric_matrix(p)
print(f"\nFisher information matrix at N(0,1):\n{fim}")
```

### SPD Manifold Quick Check

```python
from geomstats.geometry.spd_matrices import SPDMatrices
import geomstats.backend as gs

spd = SPDMatrices(n=3)
A = spd.random_point()
B = spd.random_point()
d = spd.metric.dist(A, B)
print(f"Affine-invariant distance between two 3x3 SPD matrices: {float(d):.4f}")
```

### Key Files

| Path | Description |
|---|---|
| `/Users/alice/v/worlds/g/geomstats/` | Plurigrid fork of geomstats |
| `notebooks/08_practical_methods__information_geometry.ipynb` | Fisher-Rao notebook |
| `geomstats/information_geometry/normal.py` | `NormalDistributions` manifold implementation |
| `geomstats/geometry/spd_matrices.py` | SPD matrices with affine-invariant metric |
>>>>>>> origin/main
