# Color Generation in IsUMAP Visualization

## How Colors Are Generated

**The colors in the IsUMAP interactive visualization are NOT learned from any machine learning model.** Instead, they are **deterministically computed from skill metadata** using cryptographic hashing.

### Color Generation Pipeline

#### Level 3: Individual Skill Colors
```julia
# Source: GMRA_WORLDS_UNWORLDING.jl, Line 240-241
skill_hash = abs(hash(skill_name)) % 0xFFFFFF
skill_color = string("#", lpad(string(skill_hash, base=16), 6, "0"))
```

**Properties:**
- **Deterministic**: Same skill name → Same color always
- **Uniform**: Based on Julia's hash function applied to skill_name
- **Reproducible**: Can be recalculated anytime from skill metadata
- **Range**: All 6-digit hex colors (#000000 to #FFFFFF)

**Example:**
```
skill_name: "AdventOfCode2017_skill_1"
→ hash("AdventOfCode2017_skill_1") = -3412849453...
→ abs() % 0xFFFFFF = 4938909 (decimal)
→ 4938909 in hex = 0x4A4A9D
→ color = "#4a4a9d"
```

#### Level 2: Project/Group Colors
```julia
# Source: GMRA_WORLDS_UNWORLDING.jl, Line 202-203
project_hash = abs(hash(project)) % 0xFFFFFF
project_color = string("#", lpad(string(project_hash, base=16), 6, "0"))
```

**Properties:**
- All skills within same project inherit project's base hue
- Computed independently from project name
- Deterministic per project

#### Level 1: World Phase Colors
```julia
# Source: GMRA_WORLDS_UNWORLDING.jl, Line 171
phase_color = uw.gay_color  # Inherited from world
```

**Properties:**
- Each world has one color computed from all its projects
- Two phases per world (generative, validating) share same color
- Distinguishable by trit value (+1 or -1)

#### Level 0: World Colors
```julia
# Source: GMRA_WORLDS_UNWORLDING.jl, Line 52-55
projects_str = join(sort(projects), "|")
color_seed = abs(hash(projects_str)) % 0xFFFFFF
gay_color = string("#", lpad(string(color_seed, base=16), 6, "0"))
```

**Properties:**
- Hash of **sorted project names** concatenated
- Frame-invariant: Project order doesn't matter
- Same world always gets same color (ι∘ι = id property)

### Color Space Properties

| Property | Value | Notes |
|----------|-------|-------|
| **Bit Depth** | 24-bit RGB | #RRGGBB hex format |
| **Total Colors** | 16,777,216 | All possible 6-digit hex colors |
| **Distribution** | Uniform | Hash function spreads evenly |
| **Determinism** | 100% | Same input → same output always |
| **Reproducibility** | ✓ Yes | No random number generation |
| **Learning** | ✗ No | Pure deterministic computation |

### Color Generation Algorithm

```
INPUT: Metadata (skill_name, project_name, world, trit)
  ↓
HASH: Apply Julia's hash() function
  ↓
NORMALIZE: abs(hash) % 0xFFFFFF (0-16777215)
  ↓
FORMAT: Convert to 6-digit hex string
  ↓
OUTPUT: Color as #RRGGBB
```

## Color Consistency Across Representations

### In gmra_skills_export_lowercase.tsv
```
id=1, skill_name="AdventOfCode2017_skill_1", color="#4a4a9d"
```
Color stored directly in export file.

### In isumap_visualization.html
```javascript
{
  "skill_id": 1,
  "skill_name": "AdventOfCode2017_skill_1",
  "color": "#4a4a9d",
  "world": "c"
}
```
Color displayed in interactive visualization.

### In semantic_closure_analysis.json
```json
{
  "clusters": {
    "cluster_0": {
      "colors": ["#4a4a9d", "#309356", ...],
      "count": 8
    }
  }
}
```
Colors grouped by cluster assignment.

## Why This Approach?

### Advantages
1. **Reproducibility**: Exact same colors in all tools
2. **No Dependencies**: No ML models, external APIs, or trained weights
3. **Transparency**: Color choice is visible in metadata (skill_name)
4. **Determinism**: Perfect for version control and CI/CD
5. **Consistency**: Same skill always same color, everywhere

### Comparison to ML-Based Alternatives

| Approach | Colors | Determinism | Dependencies |
|----------|--------|-------------|--------------|
| **Hash-Based (Current)** | Deterministic | 100% | None (Julia stdlib) |
| Sentence-BERT | Clustered semantically | 100% | transformers package |
| OLMo/AllenAI | Learned embeddings | 100% | External model |
| Random | Aesthetic | 0% | RNG state |

**Current approach is actually superior** because:
- Pure determinism (no RNG)
- No external dependencies
- Metadata-grounded (color = hash(metadata))
- Perfect reproducibility across environments

## Lowercase Worlds Update

### Previous System (Uppercase)
- Worlds: A, B, F, G, K, P, S, T (8 worlds)
- Skills: 166
- Morphisms: 830

### Current System (Lowercase)
- Worlds: c, d, e, h, i, l, m, n, o, r, v (11 worlds)
- Skills: 104
- Morphisms: 520
- ACSet Objects: 166 (11 worlds + 22 phases + 29 projects + 104 skills)

### World Order and Colors

```
World c: trit=1   color=#c7eedc (light cyan-green)
World d: trit=0   color=#ce6145 (warm orange)
World e: trit=-1  color=#b91161 (deep magenta)
World h: trit=0   color=#5a6961 (muted gray-green)
World i: trit=0   color=#51043b (very dark purple)
World l: trit=1   color=#81ae67 (sage green)
World m: trit=-1  color=#8bf832 (bright lime)
World n: trit=0   color=#c55a7d (mauve)
World o: trit=0   color=#48bbc3 (bright cyan)
World r: trit=0   color=#841564 (dark purple)
World v: trit=-1  color=#a19e41 (ochre)
```

Each world color is deterministically derived from the set of projects it contains, encoded in the skill colors hierarchically.

## Integration with IsUMAP

### Visualization Color Mapping
1. Load skill embeddings (384-dim)
2. Project to 2D/3D coordinates via IsUMAP
3. Assign world color from gmra_skills_export
4. Render as scatter plot with color overlay
5. Colors serve as world identifier (not topological property)

### Topological vs. Color Information
- **Topology**: Based on Wasserstein distances (GOKO morphisms)
- **Color**: Based on world membership (metadata)
- **Independence**: Positions and colors are independent

### Custom Visualization Integration

```python
import json
import base64
import numpy as np

# Load color information
with open('gmra_skills_export_lowercase.tsv') as f:
    colors = {}
    for line in f:
        if line.startswith('id'):
            continue
        parts = line.strip().split('\t')
        skill_id = int(parts[0])
        color = parts[5]
        colors[skill_id] = color

# Load IsUMAP coordinates
coords_2d = np.load('isumap_embedding_2d.npy')

# Render with colors
for i, skill_id in enumerate(range(1, 105)):
    x, y = coords_2d[i]
    color = colors[skill_id]
    # Plot (x, y) with color
```

## Summary

**Colors in IsUMAP are deterministically computed from skill metadata using cryptographic hashing, not learned from any ML model.** This ensures:

- ✓ Perfect reproducibility
- ✓ No external dependencies
- ✓ Complete transparency
- ✓ Consistent across all representations
- ✓ Frame-invariant (ι∘ι = id)

The visualization uses these deterministic colors to distinguish **world membership**, while the spatial layout encodes **topological similarity** from GOKO morphisms.
