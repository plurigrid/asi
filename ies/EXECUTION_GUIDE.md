
# Production Pipeline Execution Guide

## Prerequisites

- Julia 1.8+ with LinearAlgebra and Statistics packages
- Python 3.8+ with NumPy and pandas
- 26 world directories at `/Users/bob/worlds/`
- ~1GB disk space for intermediate files

## Complete Pipeline Execution

### Option 1: Run All Phases (Recommended)

```bash
# Phase 1-2: Load GMRA and export skills
julia production_phase1_2_gmra_worlds.jl
# Output: gmra_skills_export_mlx.tsv

# Phase 3: Create semantic embeddings
python3 production_phase3_lightweight_embed.py
# Output: skill_embeddings_lightweight.json

# Phase 4: Compute GOKO morphisms
julia production_phase4_goko_morphisms.jl
# Output: goko_morphisms.tsv

# Phase 5-6: IsUMAP projection
python3 production_phase5_isumap_projection.py
# Outputs:
#   - isumap_embedding_2d.npy
#   - isumap_embedding_3d.npy
#   - isumap_visualization_spec.json
#   - isumap_visualization.html

# Phase 7: Semantic closure analysis
python3 production_phase7_semantic_closure.py
# Output: semantic_closure_analysis.json
```

### Option 2: Run Individual Phases

Each phase can be run independently if prior outputs exist:

```bash
# Just re-run Phase 4 with existing embeddings
julia production_phase4_goko_morphisms.jl

# Just re-run Phase 5-6 with existing morphisms
python3 production_phase5_isumap_projection.py
```

## Input Files Required

```
gmra_skills_export_mlx.tsv      (from Phase 2)
  - Columns: id, skill_name, project_name, world, trit, color, embedding_text
  - 166 rows (1 header + 165 skills)

skill_embeddings_lightweight.json (from Phase 3)
  - Structure: JSON with embeddings dict, base64-encoded vectors
  - 166 embeddings, 384-dimensional

goko_morphisms.tsv              (from Phase 4)
  - Columns: source, target, wasserstein_distance, optimal_transport_cost
  - 830 rows (1 header + 829 morphisms)
```

## Output Files Generated

### Phase 2
```
gmra_skills_export_mlx.tsv
  - Master skill export
  - Used by all downstream phases
```

### Phase 3
```
skill_embeddings_lightweight.json
  - 384-dimensional embeddings
  - Base64-encoded float32 arrays
  - Deterministic (reproducible)
```

### Phase 4
```
goko_morphisms.tsv
  - k-NN graph representation
  - Wasserstein distances and OT costs
```

### Phase 5-6
```
isumap_embedding_2d.npy
  - 2D projection (166 skills × 2 dims)
  - NumPy array format

isumap_embedding_3d.npy
  - 3D projection (166 skills × 3 dims)
  - NumPy array format

isumap_visualization_spec.json
  - Complete visualization specification
  - Includes coordinates, colors, metadata for all skills

isumap_visualization.html
  - Interactive D3.js visualization
  - View in web browser: open isumap_visualization.html
```

### Phase 7
```
semantic_closure_analysis.json
  - Cluster assignments
  - Geodesic preservation metrics
  - GF(3) conservation analysis
  - Multi-scale hierarchy metrics
```

## Verification Steps

After each phase, verify outputs:

```bash
# Phase 2: Check skill count
wc -l gmra_skills_export_mlx.tsv  # Should be 167 (header + 166)

# Phase 3: Check embedding dimension
python3 -c "import json; d=json.load(open('skill_embeddings_lightweight.json')); print(f'Embeddings: {len(d["embeddings"])}, Dim: {d["embedding_dim"]}')"

# Phase 4: Check morphism count
wc -l goko_morphisms.tsv  # Should be 831 (header + 830)

# Phase 5-6: Check projection shapes
python3 -c "import numpy as np; print(f'2D: {np.load("isumap_embedding_2d.npy").shape}'); print(f'3D: {np.load("isumap_embedding_3d.npy").shape}')"

# Phase 7: Check cluster count
python3 -c "import json; d=json.load(open('semantic_closure_analysis.json')); print(f'Clusters: {d["clusters"]["n_clusters"]}')"
```

## Common Issues and Solutions

### Issue: ModuleNotFoundError: No module named 'pandas'
**Solution**: `pip install pandas`

### Issue: No Julia modules
**Solution**:
```julia
julia> using Pkg
julia> Pkg.add("LinearAlgebra")  # Usually built-in
```

### Issue: embedding_text field not found in Phase 4
**Cause**: Phase 2 export didn't run successfully
**Solution**: Re-run Phase 2: `julia production_phase1_2_gmra_worlds.jl`

### Issue: Low geodesic preservation in Phase 7
**Note**: This is expected due to heavy dimensionality reduction
**Mitigation**: Use IsUMAP instead of standard UMAP (better geodesic preservation)
**Consider**: Increasing n_neighbors in IsUMAP from 15 to 30 for less aggressive dimensionality reduction

## Performance Tuning

### To Speed Up Execution
1. **Phase 4**: Reduce k from 5 to 3 (will compute 498 morphisms instead of 830)
2. **Phase 5-6**: Reduce n_iterations from 50 to 25 (will be ~15% faster)
3. **Phase 7**: Sample fewer pairs in geodesic validation

### To Improve Geodesic Preservation
1. Increase n_neighbors in IsUMAP from 15 to 30
2. Increase n_iterations from 50 to 100
3. Use 3D projection instead of 2D (less aggressive dimensionality reduction)

### To Improve GF(3) Conservation
Note: Projection inherently breaks GF(3) conservation. To preserve it:
1. Use continuous manifold learning (not discrete projection)
2. Apply GF(3)-constrained optimization as post-processing
3. Use original GOKO distances for downstream analysis
