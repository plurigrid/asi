---
name: geomstats-fisher-rao
description: >
  Information geometry for Bayesian inference via geomstats.
  Triggers: Fisher-Rao metric, statistical manifolds, Riemannian optimization,
  Wasserstein geodesics, Gromov-Wasserstein optimal transport,
  hyperbolic embeddings, SPD matrices.
---

# geomstats-fisher-rao

Information geometry connecting geomstats to Bayesian inference and optimal transport.

## Coverage

22 notebooks in plurigrid's geomstats fork spanning:
- Information geometry (Fisher information matrix as Riemannian metric)
- Hyperbolic embeddings (Poincare ball, hyperboloid)
- Graph space (Frechet mean of graphs)
- Heisenberg group geometry
- SPD matrices (covariance manifolds)

## monad-bayes Connection

The Fisher-Rao metric is the unique Riemannian metric (up to scale) invariant under sufficient statistics:

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
