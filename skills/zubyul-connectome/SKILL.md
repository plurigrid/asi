---
name: zubyul-connectome
description: Human Connectome Project analysis bridging cortical thickness, transcription factors, and depression biomarkers. Load when working with HCP structural MRI data, cortical manifold geometry via geomstats, or Bayesian models of brain-gene relationships.
---

# zubyul-connectome

## Origin

Yuliya Zubak's undergraduate thesis: "Using Human Connectome Project data to study the relationship of cortical thickness to transcription factors for depression." R-based analysis of HCP structural MRI data. Repo: `zubyul/Nikolova_lab_data_analysis`.

## geomstats: Cortical Manifold Geometry

- Cortical surface = Riemannian manifold (genus-0 closed surface)
- Cortical thickness at each vertex = scalar field on the manifold
- Fisher-Rao metric on the statistical manifold of thickness distributions
- Geodesic regression: thickness ~ age + depression_score on SPD manifold
- geomstats `Hypersphere` / `SPDMatrices` for covariance analysis

## Hierarchical Bayesian Model

```haskell
-- Hierarchical model: cortical thickness ~ transcription + depression
corticalModel :: MonadMeasure m => HCPData -> m Parameters
corticalModel hcp = do
  mu_thickness <- normal 2.5 0.5       -- mean cortical thickness (mm)
  sigma_region <- halfNormal 0.3        -- between-region variance
  beta_transcription <- normal 0 1      -- transcription factor effect
  beta_depression <- normal 0 0.5       -- depression effect size

  forM_ (regions hcp) $ \region -> do
    offset <- normal 0 sigma_region
    let predicted = mu_thickness + offset
                  + beta_transcription * transcriptionLevel region
                  + beta_depression * depressionScore region
    factor $ normalDensity predicted 0.2 (observedThickness region)

  return (mu_thickness, beta_transcription, beta_depression)
```

## Propagator Lattice Connection

The CellValue lattice from zig-syrup/propagator.zig maps to brain states:
- `Nothing` = unmeasured cortical region (no MRI data)
- `Value` = observed thickness measurement
- `Contradiction` = conflicting measurements across sessions

Each Desikan-Killiany parcel is a `Cell`; MRI preprocessing steps are `Propagator`s that merge partial observations via `latticeMerge`.

## Vertex AI Protein Expression Bridge

- Transcription factors -> protein expression -> cortical development
- ESMFold: predict structure of depression-associated transcription factors
- AlphaFold batch: multi-protein complexes at cortical synapses

## EyeGestures Integration

- Gaze tracking (zubyul/EyeGestures) + cortical oculomotor regions
- Frontal eye field (FEF) thickness correlates with saccade patterns

## Edges

- -> monad-bayes (hierarchical Bayesian)
- -> geomstats (cortical manifold geometry)
- -> Vertex AI Protein (transcription factor folding)
- -> zubyul/WGCNA (gene-brain network bridge)
- -> zubyul/EyeGestures (gaze + cortical oculomotor)
- -> zig-syrup/propagator (CellValue lattice for brain parcels)
