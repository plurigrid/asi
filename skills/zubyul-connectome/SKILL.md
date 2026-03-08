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

## Concrete Affordances

### Clone the Upstream Repository

```bash
git clone https://github.com/zubyul/Nikolova_lab_data_analysis.git /Users/alice/v/zubyul-nikolova-lab
```

### HCP Data Access

- **ConnectomeDB portal**: https://db.humanconnectome.org/ (requires registration + data use agreement)
- **S3 bucket** (open access subset): `s3://hcp-openaccess/HCP_1200/` (use `aws s3 ls --no-sign-request`)
- **Local convention**: download structural MRI to `/Users/alice/v/data/hcp/` with subject directories like `100307/T1w/`

```bash
# List available subjects in the open-access HCP 1200 release
aws s3 ls s3://hcp-openaccess/HCP_1200/ --no-sign-request | head -20

# Download a single subject's FreeSurfer output (cortical thickness)
aws s3 cp s3://hcp-openaccess/HCP_1200/100307/T1w/100307/surf/ \
  /Users/alice/v/data/hcp/100307/surf/ \
  --recursive --no-sign-request
```

### Geodesic Regression on Cortical Thickness (geomstats)

Fit a geodesic regression model on the SPD manifold relating cortical thickness covariances to depression scores:

```python
# pip install geomstats numpy
import numpy as np
import geomstats.backend as gs
from geomstats.geometry.spd_matrices import SPDMatrices
from geomstats.learning.geodesic_regression import GeodesicRegression

gs.random.seed(42)

# SPD(3) manifold — e.g., 3x3 covariance of thickness across 3 ROIs
spd = SPDMatrices(n=3, equip=True)

# Simulated data: N subjects, each with a 3x3 thickness covariance and a depression score
N = 30
depression_scores = np.linspace(0, 1, N).reshape(-1, 1)  # predictor (scalar)

# Generate synthetic SPD points along a geodesic + noise
base_point = spd.random_point()
tangent_vec = spd.random_tangent_vec(base_point) * 0.5
y_true = np.array([
    spd.metric.exp(t * tangent_vec, base_point)
    for t in depression_scores.flatten()
])
# Add small SPD noise
noise = np.array([spd.random_tangent_vec(y) * 0.05 for y in y_true])
y_noisy = np.array([spd.metric.exp(n, y) for n, y in zip(noise, y_true)])

# Fit geodesic regression: thickness_cov ~ depression_score
gr = GeodesicRegression(
    spd,
    center_X=False,
    method="riemannian",
    initialization="frechet",
)
gr.fit(depression_scores, y_noisy)

# Predict thickness covariance for a new depression score
new_score = np.array([[0.75]])
predicted_cov = gr.predict(new_score)
print(f"Predicted thickness covariance at depression=0.75:\n{predicted_cov[0]}")
print(f"R² (manifold): {gr.score(depression_scores, y_noisy):.4f}")
```

### FreeSurfer Cortical Thickness Extraction

Extract Desikan-Killiany parcellation stats from FreeSurfer output:

```bash
# After running FreeSurfer recon-all on HCP data
export SUBJECTS_DIR=/Users/alice/v/data/hcp

# Extract cortical thickness per parcel (Desikan-Killiany atlas)
aparcstats2table --subjects 100307 100408 101107 \
  --hemi lh \
  --meas thickness \
  --tablefile /tmp/lh_thickness.tsv

# Quick look at the output
column -t -s $'\t' /tmp/lh_thickness.tsv | head -5
```

## Edges

- -> monad-bayes (hierarchical Bayesian)
- -> geomstats (cortical manifold geometry)
- -> Vertex AI Protein (transcription factor folding)
- -> zubyul/WGCNA (gene-brain network bridge)
- -> zubyul/EyeGestures (gaze + cortical oculomotor)
- -> zig-syrup/propagator (CellValue lattice for brain parcels)
