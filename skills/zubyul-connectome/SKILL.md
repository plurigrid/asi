---
name: zubyul-connectome
description: Human Connectome Project analysis bridging cortical thickness, transcription factors, and depression biomarkers. Connects zubyul's Nikolova lab neuroscience to geomstats manifold geometry, Vertex AI protein expression, and the propagator lattice.
---

# zubyul-connectome Skill

> *Cortical manifolds as propagator cells in the brain's CellValue lattice*

## Origin: zubyul/Nikolova_lab_data_analysis

Yuliya Zubak's undergraduate thesis: "Using Human Connectome Project data to
study the relationship of cortical thickness to transcription factors for
depression." R-based analysis of HCP structural MRI data.

## What's Possible

### 1. geomstats: Cortical Manifold Geometry
- Cortical surface = Riemannian manifold (genus-0 closed surface)
- Cortical thickness at each vertex = scalar field on the manifold
- Fisher-Rao metric on the statistical manifold of thickness distributions
- Geodesic regression: thickness ~ age + depression_score on SPD manifold
- geomstats `Hypersphere` / `SPDMatrices` for covariance analysis

### 2. monad-bayes: Hierarchical Bayesian Model
```haskell
-- Hierarchical model: cortical thickness ~ transcription + depression
corticalModel :: MonadMeasure m => HCPData -> m Parameters
corticalModel hcp = do
  -- Population-level priors
  mu_thickness <- normal 2.5 0.5       -- mean cortical thickness (mm)
  sigma_region <- halfNormal 0.3        -- between-region variance
  beta_transcription <- normal 0 1      -- transcription factor effect
  beta_depression <- normal 0 0.5       -- depression effect size

  -- Region-level: each Desikan-Killiany parcel
  forM_ (regions hcp) $ \region -> do
    offset <- normal 0 sigma_region
    let predicted = mu_thickness + offset
                  + beta_transcription * transcriptionLevel region
                  + beta_depression * depressionScore region
    factor $ normalDensity predicted 0.2 (observedThickness region)

  return (mu_thickness, beta_transcription, beta_depression)
```

### 3. Propagator Lattice Connection
The CellValue lattice from zig-syrup/propagator.zig maps to brain states:
- `Nothing` = unmeasured cortical region (no MRI data)
- `Value` = observed thickness measurement
- `Contradiction` = conflicting measurements across sessions

Each Desikan-Killiany parcel is a `Cell`; MRI preprocessing steps are
`Propagator`s that merge partial observations via `latticeMerge`.

AGM belief revision (continuation.zig):
- `expand` = add new parcels from additional MRI acquisitions
- `contract` = remove artifact-contaminated regions
- `revise` = Levi identity update when depression status changes

### 4. Vertex AI Protein Expression Bridge
- Transcription factors -> protein expression -> cortical development
- ESMFold: predict structure of depression-associated transcription factors
- AlphaFold batch: multi-protein complexes at cortical synapses
- GameOpt (Bal et al. 2024): optimize protein-cortex interaction network
  as combinatorial game on residue positions

### 5. EyeGestures Integration
- Gaze tracking (zubyul/EyeGestures) + cortical oculomotor regions
- Frontal eye field (FEF) thickness correlates with saccade patterns
- monad-bayes Kalman filter on gaze stream, informed by cortical priors
- Gay.jl SPI color at gaze fixation point = neurofeedback signal

### 6. GF(3) Trit Classification
| Component | Trit | Role |
|-----------|------|------|
| HCP MRI data | +1 | Generation (observation) |
| geomstats manifold | 0 | Coordination (geometry) |
| monad-bayes posterior | -1 | Validation (inference) |

Conservation: +1 + 0 + (-1) = 0

## Edges in Interactome TUI
- -> monad-bayes (w=0.75, hierarchical Bayesian)
- -> geomstats (w=0.85, cortical manifold geometry)
- -> Vertex AI Protein (w=0.70, transcription factor folding)
- -> zubyul/WGCNA (w=0.90, gene-brain network bridge)
- -> zubyul/EyeGestures (w=0.60, gaze + cortical oculomotor)
- -> zig-syrup/propagator (w=0.65, CellValue lattice for brain parcels)

## Trit: 0 (ERGODIC - bridges neuroscience to interactome)
