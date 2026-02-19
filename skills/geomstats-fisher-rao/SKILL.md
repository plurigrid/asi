---
name: geomstats-fisher-rao
description: Information geometry for Bayesian inference. Fisher-Rao metric on statistical manifolds, Riemannian optimization for model selection, Wasserstein geodesics connecting geomstats to Gromov-Wasserstein optimal transport.
---

# geomstats-fisher-rao Skill

> *The natural metric on probability distributions is the Fisher-Rao metric*

## What It Covers

22 notebooks in plurigrid's geomstats fork spanning:
- Information geometry (Fisher information matrix as Riemannian metric)
- Hyperbolic embeddings (Poincare ball, hyperboloid)
- Graph space (Frechet mean of graphs)
- Heisenberg group geometry
- SPD matrices (covariance manifolds)

## monad-bayes Connection

The Fisher-Rao metric is the unique Riemannian metric (up to scale) that is
invariant under sufficient statistics. This means:

```
MonadDistribution m => FisherRao (distribution m)
```

Every `score`/`factor` call in monad-bayes implicitly moves along a geodesic
on the Fisher-Rao manifold. The MCMC acceptance ratio is the exponential map.

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
