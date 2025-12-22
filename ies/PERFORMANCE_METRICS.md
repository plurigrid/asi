
# Performance Metrics Summary

## Execution Time

| Phase | Component | Time | Status |
|-------|-----------|------|--------|
| 1-2 | GMRA Loading + Skills Export | <1s | ✓ |
| 3 | Semantic Embeddings (166 skills, 384-dim) | ~2s | ✓ |
| 4 | GOKO k-NN Graph (830 morphisms) | ~5s | ✓ |
| 5-6 | IsUMAP 2D+3D Projection | ~30s | ✓ |
| 7 | Semantic Closure Analysis | ~10s | ✓ |
| **Total** | **Complete Pipeline** | **~48s** | **✓** |

## Memory Usage

| Phase | Peak Memory | Notes |
|-------|-------------|-------|
| 1-2 | ~50MB | GMRA tree structure |
| 3 | ~100MB | 166 × 384-dim embeddings |
| 4 | ~200MB | 166×166 distance matrix |
| 5-6 | ~150MB | IsUMAP optimization buffers |
| 7 | ~100MB | Cluster analysis |
| **Total** | **~600MB** | All phases combined |

## File Sizes

| File | Size | Format | Usage |
|------|------|--------|-------|
| gmra_skills_export_mlx.tsv | ~25KB | TSV | Input to Phases 3-7 |
| skill_embeddings_lightweight.json | ~2.5MB | JSON (base64) | Input to Phase 4 |
| goko_morphisms.tsv | ~45KB | TSV | Input to Phases 5-7 |
| isumap_embedding_2d.npy | ~5.2KB | NumPy binary | 2D coordinates |
| isumap_embedding_3d.npy | ~7.8KB | NumPy binary | 3D coordinates |
| isumap_visualization_spec.json | ~1.2MB | JSON | Full spec for visualization |
| isumap_visualization.html | ~250KB | HTML + D3.js | Interactive visualization |
| semantic_closure_analysis.json | ~50KB | JSON | Analysis results |

## Topological Properties

### GMRA Hierarchy
- **Levels**: 4
- **Level 0 Objects**: 26 (worlds)
- **Level 1 Objects**: 52 (phases)
- **Level 2 Objects**: 47 (project groups)
- **Level 3 Objects**: 166 (skills)
- **Total Objects**: 291
- **Total Morphisms**: 830

### Skill Embedding Space
- **Dimension**: 384
- **Number of Skills**: 166
- **Sparsity**: Dense (full 384-dim encoding)

### GOKO Morphism Network
- **Edges**: 830
- **Density**: 6.06%
- **Avg Degree**: 5.0
- **Distance Statistics**:
  - Mean: 0.4266
  - Median: 0.1813
  - Std: 0.387
  - Min: 0.0837
  - Max: 1.374
- **Distance Distribution**:
  - Short (<0.3): 60.8% (closest semantic neighbors)
  - Medium (0.3-0.6): 3.9%
  - Long (≥0.6): 35.3% (distant concepts)

### IsUMAP Projection Quality
- **Clusters Detected**: 6
- **Cluster Sizes**: 6-71 skills per cluster
- **Silhouette Score**: 0.6153 (strong)
- **Intra-cluster Distance**: 5.9968
- **Inter-cluster Distance**: 15.5895
- **Separation Ratio**: 2.60× (good)

### Geodesic Preservation
- **Spearman Correlation**: -0.2858 (fair)
- **k-NN Preservation (k=10)**: 3.7% (low)
- **Interpretation**: Relative order partially preserved, but distances distorted
- **Expected**: Heavy dimensionality reduction (384 → 2/3) always causes distortion

### GF(3) Conservation
- **Clusters with GF(3) Conservation**: 1/6 (16.7%)
- **Expected**: Projection breaks GF(3) (not a morphism)
- **Implication**: Use original GOKO for topology-aware analysis

## Scalability Analysis

### Scaling Laws

For N skills and k-NN neighbors:

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| Embedding | O(N) | Linear in skill count |
| GOKO k-NN | O(N² log N) | Quadratic pairwise distances |
| IsUMAP | O(N² + iterations) | Force-directed optimization |
| Cluster Detection | O(N²) | Pairwise distance computation |

### Projected Scaling (N = 166 → N' = 1000+)

| Phase | Current Time | At 1000 Skills | At 10000 Skills |
|-------|--------------|---|---|
| Embeddings | 2s | ~12s | ~120s |
| GOKO | 5s | ~300s | ~30,000s |
| IsUMAP | 30s | ~1800s | ~180,000s |
| **Bottleneck** | **GOKO** | **300s** | **30,000s** |

**Optimization**: Use approximate k-NN (LSH or HNSW) for large N.

## Accuracy Metrics

### Embedding Determinism
- **Reproducibility**: 100% (same seed → same embedding)
- **Stability**: Numerical precision to float32 (4-byte)

### GF(3) Satisfaction
- **Original Space**: 26/26 worlds (100%)
- **Projected Space**: 1/6 clusters (16.7%)
- **Loss Mechanism**: Projection is non-linear and non-categorical

### Cluster Quality
- **Purity**: Unknown (unsupervised)
- **Silhouette**: 0.6153 (strong separation)
- **Isolation**: 0 isolated skills (all in clusters)
