# Integration Guide: GMRA + GOKO + IsUMAP Skill Lattice

## Overview

This guide explains how to integrate the production GMRA skill lattice system into your ASI architecture.

## Quick Start

The complete pipeline produces 8 core data artifacts:

```
gmra_skills_export_mlx.tsv              # Skill metadata (166 skills)
skill_embeddings_lightweight.json        # 384-dim embeddings
goko_morphisms.tsv                       # 830 k-NN morphisms
isumap_embedding_2d.npy                 # 2D projection
isumap_embedding_3d.npy                 # 3D projection
isumap_visualization_spec.json           # Full visualization spec
isumap_visualization.html                # Interactive HTML visualization
semantic_closure_analysis.json           # Cluster analysis results
```

## Integration Points

### 1. Embedding-Based Similarity

Use the 384-dimensional embeddings for skill similarity:

```python
import json
import numpy as np
import base64

# Load embeddings
with open('skill_embeddings_lightweight.json') as f:
    data = json.load(f)
    embeddings = data['embeddings']

# Decode specific skill embedding
skill_id = 1
embedding_b64 = embeddings[str(skill_id)]
embedding_bytes = base64.b64decode(embedding_b64)
embedding = np.frombuffer(embedding_bytes, dtype=np.float32)

# Compute similarity to another skill
skill_id_2 = 2
embedding_2_b64 = embeddings[str(skill_id_2)]
embedding_2_bytes = base64.b64decode(embedding_2_b64)
embedding_2 = np.frombuffer(embedding_2_bytes, dtype=np.float32)

similarity = np.dot(embedding, embedding_2)  # Cosine similarity (both unit-norm)
```

### 2. GOKO Morphism Graph

Use GOKO morphisms to find related skills and progression paths:

```python
import pandas as pd

# Load morphisms
morphisms = pd.read_csv('goko_morphisms.tsv', sep='\t')

# Find skills related to skill ID 42
related = morphisms[morphisms['source'] == 42]
related = related.sort_values('wasserstein_distance')

print("Skills most similar to skill 42:")
for _, row in related.head(5).iterrows():
    target_id = int(row['target'])
    distance = row['wasserstein_distance']
    cost = row['optimal_transport_cost']
    print(f"  → Skill {target_id} (distance: {distance:.4f})")

# Build progression path (k-NN traversal)
def find_progression_path(start_id, n_steps=5):
    path = [start_id]
    current = start_id

    for _ in range(n_steps):
        next_skills = morphisms[morphisms['source'] == current]
        if next_skills.empty:
            break

        # Choose skill with smallest distance (closest progression)
        next_id = int(next_skills.loc[next_skills['wasserstein_distance'].idxmin(), 'target'])
        if next_id not in path:
            path.append(next_id)
            current = next_id
        else:
            break

    return path

path = find_progression_path(1, n_steps=10)
print(f"Learning progression: {' → '.join(map(str, path))}")
```

### 3. Skill Clustering and Grouping

Use cluster assignments to group skills by topic:

```python
import json

# Load cluster analysis
with open('semantic_closure_analysis.json') as f:
    analysis = json.load(f)

# Get cluster assignments
cluster_assignments = analysis['clusters']['cluster_assignments']

# Group skills by cluster
clusters = {}
for skill_idx_str, cluster_id in cluster_assignments.items():
    if cluster_id not in clusters:
        clusters[cluster_id] = []
    clusters[cluster_id].append(int(skill_idx_str))

# Load skill metadata
skills_df = pd.read_csv('gmra_skills_export_mlx.tsv', sep='\t')

# Print cluster contents
for cluster_id in sorted(clusters.keys()):
    skill_indices = clusters[cluster_id]
    print(f"\nCluster {cluster_id} ({len(skill_indices)} skills):")

    for idx in skill_indices[:3]:  # Show first 3
        skill_row = skills_df[skills_df['id'] == idx]
        if not skill_row.empty:
            name = skill_row.iloc[0]['skill_name']
            project = skill_row.iloc[0]['project_name']
            print(f"  • {name} (Project: {project})")

    if len(skill_indices) > 3:
        print(f"  ... and {len(skill_indices) - 3} more")
```

### 4. Visualization Integration

Embed the interactive visualization in your web application:

```html
<!-- Option 1: Standalone visualization -->
<iframe src="isumap_visualization.html"
        width="1000" height="700"
        frameborder="0"></iframe>

<!-- Option 2: Use visualization spec to create custom visualization -->
<div id="skill-space"></div>

<script>
fetch('isumap_visualization_spec.json')
  .then(r => r.json())
  .then(spec => {
    // spec.projections.2d.coordinates - 2D coordinates for all skills
    // spec.skills - detailed metadata for each skill

    // Your custom D3/Three.js visualization code here
    console.log(`Loaded ${spec.skills.length} skills`);

    // Example: create force-directed graph
    const skills = spec.skills;
    const coords = spec.projections['2d'].coordinates;

    // Use coords and skills.metadata to render
  });
</script>
```

### 5. Curriculum Design

Use skill hierarchy and distances for adaptive curriculum:

```python
import numpy as np

# Load embeddings and morphisms
embeddings_dict = {}  # Load as shown above
morphisms_df = pd.read_csv('goko_morphisms.tsv', sep='\t')
clusters = get_cluster_assignments()  # Load as shown above

def design_curriculum(starting_skill_id, difficulty_level='beginner'):
    """Design learning path based on skill relationships."""

    progression = []
    current = starting_skill_id

    # Difficulty parameters
    if difficulty_level == 'beginner':
        max_distance = 0.3  # Only very close skills
        path_length = 5
    elif difficulty_level == 'intermediate':
        max_distance = 0.6  # Moderate progression
        path_length = 10
    else:  # advanced
        max_distance = 1.0  # Full range
        path_length = 15

    for step in range(path_length):
        # Find next skill within difficulty constraints
        related = morphisms_df[morphisms_df['source'] == current]
        candidates = related[
            (related['wasserstein_distance'] <= max_distance) &
            (related['wasserstein_distance'] > 0)
        ]

        if candidates.empty:
            break

        # Prefer skills not yet learned
        candidates = candidates.sort_values('wasserstein_distance')

        for _, row in candidates.iterrows():
            next_id = int(row['target'])
            if next_id not in progression:
                progression.append(next_id)
                current = next_id
                break
        else:
            break

    return progression

# Create curriculum for new learner
curriculum = design_curriculum(starting_skill_id=1, difficulty_level='beginner')
print(f"Recommended learning path ({len(curriculum)} skills):")
for i, skill_id in enumerate(curriculum, 1):
    print(f"  {i}. Skill {skill_id}")
```

### 6. Quality Metrics Access

Monitor system quality and performance:

```python
import json

# Load quality metrics
with open('PRODUCTION_SUMMARY.json') as f:
    summary = json.load(f)

# Access quality metrics
quality = summary['quality_metrics']
print(f"Cluster Silhouette: {quality['cluster_silhouette']}")
print(f"Geodesic Preservation (Spearman r): {quality['geodesic_preservation']}")
print(f"GF(3) Conservation: {quality['gf3_conservation_percentage']}%")

# Performance metrics
arch = summary['architecture']
print(f"\nArchitecture:")
print(f"  Hierarchy Levels: {arch['levels']}")
print(f"  Total Objects: {arch['total_objects']}")
print(f"  Embedding Dimension: {arch['embedding_dimension']}")
print(f"  Morphisms: {arch['total_objects']} skills × {arch['morphisms']}")
```

## Advanced Integration

### Custom Skill Embedding Updates

To add new skills to the system:

```python
import hashlib
import numpy as np

def create_skill_embedding(skill_name, project_name, world, trit, dimension=384):
    """Create embedding for new skill using same method as training."""

    # World encoding
    world_id = (ord(world) - ord('A')) % 50
    world_vec = np.zeros(50)
    if 0 <= world_id < 50:
        world_vec[world_id] = 1.0

    # Trit encoding
    trit_vec = np.array([trit, trit**2, np.tanh(trit * 2)])
    trit_vec = np.tile(trit_vec, 30)[:90]

    # Project encoding
    project_hash = hashlib.sha256(project_name.encode()).digest()
    project_seed = int.from_bytes(project_hash[:8], 'big') % (2**31)
    project_rng = np.random.RandomState(project_seed)
    project_vec = project_rng.normal(0, 0.1, 100)

    # Skill encoding
    skill_hash = hashlib.sha256(skill_name.encode()).digest()
    skill_seed = int.from_bytes(skill_hash[:8], 'big') % (2**31)
    skill_rng = np.random.RandomState(skill_seed)
    skill_vec = skill_rng.normal(0, 0.1, 100)

    # Combine
    combined = np.concatenate([world_vec, trit_vec, project_vec, skill_vec[:54]])
    if len(combined) < dimension:
        combined = np.concatenate([combined, np.zeros(dimension - len(combined))])
    else:
        combined = combined[:dimension]

    # Normalize
    embedding = combined / (np.linalg.norm(combined) + 1e-8)
    return embedding
```

### Hierarchical Skill Relationships

Access the multi-level hierarchy:

```python
def get_skill_hierarchy(skill_id):
    """Get hierarchical context for a skill."""

    skills_df = pd.read_csv('gmra_skills_export_mlx.tsv', sep='\t')
    skill_row = skills_df[skills_df['id'] == skill_id]

    if skill_row.empty:
        return None

    skill = skill_row.iloc[0]

    return {
        'skill': {
            'id': skill['id'],
            'name': skill['skill_name'],
            'trit': skill['trit']
        },
        'project': skill['project_name'],
        'world': skill['world'],
        'color': skill['color'],
        'context': {
            'level_0': f"World {skill['world']}",
            'level_1': f"Phase (trit={skill['trit']})",
            'level_2': f"Project {skill['project_name']}",
            'level_3': f"Skill {skill['skill_name']}"
        }
    }
```

## Performance Considerations

### Memory Usage
- Embeddings: 166 × 384 × 4 bytes = ~255 KB
- Morphisms: 830 edges = ~20 KB
- Distance matrix (if computed): 166 × 166 × 8 bytes = ~220 KB
- Total in-memory: <1 MB

### Computation Time
- Loading embeddings: <100ms
- Finding k-NN neighbors: ~50ms per query
- Similarity computation: <1ms per pair
- Cluster lookup: <1ms

### Scaling
Current system:
- 166 skills in 48 seconds
- 6 clusters with strong separation

For 1000+ skills:
- Implement LSH (Locality Sensitive Hashing) for k-NN
- Use approximate distance computation
- Cache projection coordinates

## Troubleshooting

### Issue: Embeddings not loading
**Solution**: Verify base64 decoding:
```python
import base64
b64_str = embeddings[str(skill_id)]
decoded = base64.b64decode(b64_str)
assert len(decoded) == 384 * 4  # 384 float32 values
```

### Issue: Morphism distances seem inverted
**Solution**: Check that distances are Wasserstein, not similarity:
```python
# Lower distance = more similar
morphisms.sort_values('wasserstein_distance').head()
```

### Issue: Clusters don't match expectations
**Solution**: Review clustering parameters in semantic_closure_analysis.json:
- eps=1.5 (neighborhood radius)
- min_samples=3 (minimum cluster size)
- Silhouette score: 0.6153 (quality metric)

## Next Steps

1. **Visualization**: Open `isumap_visualization.html` in a web browser
2. **Analysis**: Review `semantic_closure_analysis.json` for cluster details
3. **Integration**: Use the code examples above to integrate into your system
4. **Scaling**: Plan LSH/HNSW implementation for >1000 skills
5. **Monitoring**: Track quality metrics as new skills are added

## Documentation

For detailed information, see:
- `ARCHITECTURE.md` - System design overview
- `EXECUTION_GUIDE.md` - How to run the pipeline
- `PERFORMANCE_METRICS.md` - Detailed performance analysis
- `DEPLOYMENT_CHECKLIST.md` - Verification checklist
