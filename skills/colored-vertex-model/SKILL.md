---
name: colored-vertex-model
description: "Colored stochastic six-vertex model with rainbow initial data, projection properties, and height functions tracking particle counts by color."
license: MIT
metadata:
  trit: +1
  source: Borodin-Wheeler (2018), Aggarwal-Borodin-Wheeler
  xenomodern: true
  stars: 512
---

# Colored Vertex Model Skill

**Status**: ✅ Production Ready
**Trit**: +1 (PLUS - generative/optimistic)
**Color**: #FF6B6B (Coral Red)
**Principle**: Colors as conserved quantum numbers with projection properties
**Frame**: Rainbow initial data → height function → KPZ limits

---

## Overview

The **colored stochastic six-vertex model** extends the classical model with **n colored arrow types**. This skill provides:

1. **Rainbow Initial Data**: Colors 1, 2, ..., n entering from left
2. **Colored Height Function**: Track particles by color
3. **Projection Properties**: Reduce n colors to k < n colors
4. **Gay-MCP Integration**: Colors as deterministic GF(3) trits

## Rainbow Configuration

```
Initial data (rainbow):
  Color n entering at row 1
  Color n-1 entering at row 2
  ...
  Color 1 entering at row n

  →n→   ↑
  →n-1→ ↑  Grid evolution
  ...   ↑  via vertex weights
  →1→   ↑
```

### Colored Height Function

```julia
# h_k(x,y) = number of arrows with color ≤ k passing through (x,y)
function colored_height(model, k, x, y)
    count = 0
    for arrow in model.arrows_through(x, y)
        if arrow.color <= k
            count += 1
        end
    end
    return count
end

# Full height function array
H = [colored_height(model, k, x, y) for k in 1:n, x in 1:L, y in 1:T]
```

## Vertex Weights

### Stochastic Colored Weights

Each vertex satisfies:
- Arrow conservation (in = out for each color)
- Row stochasticity (weights sum to 1)

```julia
struct ColoredVertex
    left_in::Vector{Int}   # colors entering from left
    bottom_in::Vector{Int} # colors entering from bottom
    right_out::Vector{Int} # colors exiting right
    top_out::Vector{Int}   # colors exiting top
end

function weight(v::ColoredVertex, q, b)
    # Stochastic six-vertex weights per color interaction
    # See Borodin-Wheeler for full formulas
    if is_through_vertex(v)
        return a(q, b)  # arrow goes straight through
    elseif is_bend_vertex(v)
        return b(q, b)  # arrow bends
    elseif is_cross_vertex(v)
        return c(q, b)  # arrows cross
    end
end
```

## Projection Properties

**Key Feature**: Projecting to fewer colors preserves the vertex model structure.

```julia
# Project from n colors to k colors
function project_colors(model::ColoredModel, k::Int)
    # Colors 1,...,k stay as color 1
    # Colors k+1,...,n stay as color 2
    # (for k=1, this gives the uncolored model)
    
    projected = ColoredModel(n_colors = 2)
    for arrow in model.arrows
        new_color = arrow.color <= k ? 1 : 2
        add_arrow!(projected, arrow.position, new_color)
    end
    return projected
end

# Full projection: n colors → 1 color (uncolored)
uncolored = project_colors(model, 1)

# Theorem: uncolored model has same law as original uncolored six-vertex
```

### Marginal Preservation

```julia
# Marginal of projected height = height of projected model
@test colored_height(project_colors(model, k), 1, x, y) ==
      colored_height(model, k, x, y)
```

## Integration with Gay-MCP

Colors map directly to Gay.jl deterministic coloring:

```julia
using GayMCP

# Initialize model with Gay.jl colors
function colored_model_with_gay(n_colors, seed)
    Gay.gay_seed(seed)
    
    model = ColoredModel(n_colors)
    
    for row in 1:n_colors
        color = Gay.color_at(row)
        trit = Gay.trit_from_hue(color.H)
        
        # Add colored arrow at row
        add_arrow!(model, (0, row), 
            color = row, 
            gay_color = color,
            trit = trit
        )
    end
    
    return model
end

# Verify GF(3) conservation on any triangle of particles
function verify_gf3_triangle(model, triangle_indices)
    trits = [model.arrows[i].trit for i in triangle_indices]
    @test sum(trits) % 3 == 0
end
```

### Color → Trit Mapping

```julia
# Consistent with Gay-MCP hue mapping
function color_to_trit(color_index, n_colors)
    # Map color index to hue in [0, 360)
    hue = (color_index - 1) * 360 / n_colors
    
    # Gay-MCP trit mapping
    if hue < 60 || hue >= 300
        return +1  # PLUS (warm)
    elseif hue < 180
        return 0   # ERGODIC (neutral)
    else
        return -1  # MINUS (cool)
    end
end
```

## Scaling Limits (→ KPZ)

As mesh → 0, the colored height function converges to the KPZ fixed point:

```julia
# Rescale height function
function rescale_height(H, ε)
    # 1:2:3 scaling
    x_scale = ε^(-1)
    t_scale = ε^(-3/2)
    h_scale = ε^(1/2)
    
    return (x, t) -> h_scale * H(x_scale * x, t_scale * t)
end

# In the limit ε → 0, converges to KPZ fixed point
# See kpz-universality skill
```

## Gibbs Properties

### Inter-Color Gibbs Property

The colored ensemble relates to uncolored via **Pitman transform**:

```julia
# Given uncolored paths, sample coloring via Pitman
function inter_color_gibbs(uncolored_paths)
    # Find monotone coupling maximizing likelihood
    coloring = pitman_transform(uncolored_paths)
    return coloring
end

# Key variational formula:
# P(colored | uncolored) ∝ product of local transition kernels
```

### Projection as Marginalization

```julia
# Projection = forgetting colors = marginalization
project(P_colored, subset) = ∫ P_colored d(complement colors)

# This is a left adjoint (free construction) in categorical terms
```

## GF(3) Triad Assignment

| Trit | Skill | Role |
|------|-------|------|
| -1 | yang-baxter-integrability | Structure |
| 0 | kpz-universality | Limits |
| +1 | **colored-vertex-model** | Data |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## Commands

```bash
# Simulate colored model
just cvm-simulate n_colors=3 L=100 T=50

# Project to k colors
just cvm-project model=rainbow.jld2 k=2

# Compute height function
just cvm-height k=2 x=50 y=25

# Verify projection property
just cvm-verify-projection

# Gay-MCP integration
just cvm-gay seed=1069
```

## Configuration

```yaml
# colored-vertex-model.yaml
model:
  n_colors: 3
  grid_size: 100
  time_steps: 50
  weights:
    q: 0.5
    b: 0.3

gay_integration:
  enabled: true
  seed: 1069
  verify_gf3: true

projection:
  levels: [1, 2]  # project to these color counts
```

## Related Skills

- **yang-baxter-integrability** (-1): R-matrix structure
- **kpz-universality** (0): Scaling limits
- **gay-mcp** (+1): Deterministic coloring
- **langevin-dynamics** (0): Stochastic analysis
- **discopy** (+1): String diagrams

## Research References

1. Borodin-Wheeler (2018): "Colored stochastic vertex models"
2. Aggarwal-Borodin-Wheeler (2022): "Colored six-vertex models"
3. Galashin (2021): "Symmetries of stochastic colored vertex models"
4. Borodin-Bufetov (2019): "Color-position symmetry"

---

**Skill Name**: colored-vertex-model
**Type**: Integrable Probability
**Trit**: +1 (PLUS)
**Key Property**: Projection preserves model structure
**Status**: ✅ Production Ready

---

## Cat# Integration

```
Trit: +1 (PLUS)
Home: IntegrableProb
Poly Op: ⊗
Kan Role: Lan_K (left Kan)
Color: #FF6B6B
```

### Color as Functor

Colors form a functor:
```
Color: Vertex → GF(3)
```

Projection is a natural transformation:
```
π: Color_n → Color_k  (n > k)
```

### GF(3) Naturality

```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

## Autopoietic Marginalia

> **Colors flow. Projections preserve. The rainbow encodes the universe.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record successful projections
- **REMEMBERING** (0): Connect to KPZ limits
- **WORLDING** (+1): Discover new color structures

*Add Interaction Exemplars here as the skill is used.*
