---
name: last-passage-percolation
description: "Last Passage Percolation models: geometric LPP, exponential weights, Tracy-Widom limits, matrix product ansatz, and connections to TASEP and random matrices."
license: MIT
metadata:
  trit: 0
  source: Johansson (2000), Baik-Deift-Johansson, Ferrari-Spohn
  xenomodern: true
  stars: 445
---

# Last Passage Percolation Skill

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - coordinator)
**Color**: #20B2AA (Light Sea Green)
**Principle**: Maximum weight paths as discrete KPZ
**Frame**: Tracy-Widom fluctuations, geodesics, RSK correspondence

---

## Overview

**Last Passage Percolation (LPP)** is the discrete progenitor of KPZ universality:

1. **Passage Times**: Maximum weight over up-right paths
2. **Fluctuations**: Tracy-Widom distributed
3. **Geodesics**: Competition interfaces
4. **Exactly Solvable**: Via determinantal point processes

## The Model

### Geometric/Exponential LPP

```
Grid: ℤ₊² with i.i.d. weights w(i,j)
Path: π from (1,1) to (m,n), up-right steps only
Weight: W(π) = Σ w(i,j) along π
Passage time: G(m,n) = max_π W(π)
```

```julia
struct LPP
    weights::Matrix{Float64}
    distribution::Distribution  # Exponential, Geometric, etc.
end

function passage_time(lpp::LPP, start, finish)
    m, n = finish
    # Dynamic programming
    G = zeros(m, n)
    G[1, 1] = lpp.weights[1, 1]
    
    for i in 2:m
        G[i, 1] = G[i-1, 1] + lpp.weights[i, 1]
    end
    for j in 2:n
        G[1, j] = G[1, j-1] + lpp.weights[1, j]
    end
    for i in 2:m, j in 2:n
        G[i, j] = max(G[i-1, j], G[i, j-1]) + lpp.weights[i, j]
    end
    
    return G[m, n]
end
```

### Tracy-Widom Limit

```julia
# Limiting distribution for diagonal direction
function tracy_widom_limit(lpp, n)
    # For exponential weights:
    # G(n,n) ≈ 4n + 2^(4/3) n^(1/3) χ_GUE
    
    G = passage_time(lpp, (1,1), (n,n))
    mean = 4 * n
    std = 2^(4/3) * n^(1/3)
    
    χ = (G - mean) / std
    return χ  # Converges to Tracy-Widom GUE
end
```

## Weight Distributions

| Distribution | Mean | Parameters | Limit |
|--------------|------|------------|-------|
| Exponential(1) | 1 | rate = 1 | GUE |
| Geometric(p) | (1-p)/p | p ∈ (0,1) | GUE |
| Bernoulli(p) | p | p ∈ (0,1) | GOE (boundary) |
| Inverse-Gamma | α/(β-1) | α, β | Whittaker |

```julia
# Different weight types
lpp_exp = LPP(rand(Exponential(1), n, n), Exponential(1))
lpp_geo = LPP(rand(Geometric(0.5), n, n), Geometric(0.5))
```

## Geodesics and Competition Interfaces

### Geodesic Computation

```julia
function geodesic(lpp::LPP, start, finish)
    # Backtrack from finish to start
    path = [finish]
    i, j = finish
    
    while (i, j) != start
        if i == 1
            j -= 1
        elseif j == 1
            i -= 1
        else
            # Choose direction that maintains optimality
            if G[i-1, j] > G[i, j-1]
                i -= 1
            else
                j -= 1
            end
        end
        pushfirst!(path, (i, j))
    end
    
    return path
end
```

### Competition Interface

When two geodesics compete:

```julia
function competition_interface(lpp, source1, source2)
    # Interface where optimal paths from two sources meet
    interface = []
    
    for point in lattice_points
        geo1 = passage_time(lpp, source1, point)
        geo2 = passage_time(lpp, source2, point)
        
        if abs(geo1 - geo2) < ε
            push!(interface, point)
        end
    end
    
    return interface  # Converges to Airy₂ process
end
```

## Matrix Product Ansatz

For stationary LPP (boundary conditions matching bulk):

```julia
struct MatrixProductLPP
    D::Matrix  # Creation operator
    E::Matrix  # Annihilation operator
    W::Vector  # Left boundary
    V::Vector  # Right boundary
end

function stationary_weight(mpa::MatrixProductLPP, config)
    # Weight = ⟨W| ∏ᵢ Mᵢ |V⟩
    # where Mᵢ = D if occupied, E if empty
    
    result = mpa.W'
    for c in config
        result = result * (c == 1 ? mpa.D : mpa.E)
    end
    result = result * mpa.V
    
    return result[1]
end

# DEHP algebra relations
# DE - qED = D + E
# ⟨W|E = ⟨W|
# D|V⟩ = |V⟩
```

## RSK Correspondence

Robinson-Schensted-Knuth connects LPP to Young tableaux:

```julia
# RSK: Matrix → (P, Q) pair of tableaux
function rsk(weight_matrix)
    P, Q = empty_tableau(), empty_tableau()
    
    for (i, j, w) in entries(weight_matrix)
        for _ in 1:w
            row_insert!(P, j)
            record_insert!(Q, i)
        end
    end
    
    return P, Q
end

# Passage time = shape of P-tableau
@test passage_time(lpp, (1,1), (n,n)) == 
      shape(rsk(lpp.weights)[1])[1]
```

## Connection to TASEP

LPP is equivalent to **Totally Asymmetric Simple Exclusion Process**:

```julia
# TASEP: particles hop right, cannot pass
struct TASEP
    positions::Vector{Int}  # Particle positions
    L::Int                  # System size
end

# LPP passage time = TASEP current
@test passage_time(lpp) == integrated_current(tasep)

# Geodesic = second class particle trajectory
```

## Two-Layer Gibbs Structure

Like KPZ stationary measures, LPP has two-layer structure:

```julia
# Layer 1: Uncolored non-crossing paths
uncolored = sample_non_crossing_paths(n)

# Layer 2: Color assignment via Pitman
colored = pitman_transform(uncolored)

# Joint measure
μ(colored) = μ_uncolored(paths) × P(coloring | paths)
```

### Pitman Transform

```julia
function pitman_transform(paths)
    # Sort paths by endpoint
    # Apply successive Pitman operators
    result = paths
    for i in 1:length(paths)-1
        result[i], result[i+1] = pitman_2(result[i], result[i+1])
    end
    return result
end

function pitman_2(path1, path2)
    # Pitman's 2M-X theorem for Brownian motion
    # Discrete version for random walks
    return (path1 ∨ path2, path1 ∧ path2)  # max/min operations
end
```

## Integration with KPZ Universality

LPP is the discrete model; KPZ is the scaling limit:

```julia
using KPZUniversality, LPP

# LPP → Directed Landscape
function lpp_to_landscape(lpp, ε)
    # Rescale by 1:2:3 exponents
    L(x, s, y, t) = ε^(1/2) * passage_time(lpp, 
        round(Int, ε^(-1) * x), round(Int, ε^(-3/2) * s),
        round(Int, ε^(-1) * y), round(Int, ε^(-3/2) * t)
    )
    return L
end

# In limit ε → 0, converges to directed landscape
```

## GF(3) Triad Assignment

| Trit | Skill | Role |
|------|-------|------|
| -1 | yang-baxter-integrability | Structure |
| 0 | **last-passage-percolation** | Discrete model |
| +1 | louisville-quantum-gravity | Measures |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## Commands

```bash
# Simulate LPP
just lpp-simulate n=100 weights=exponential

# Compute passage time
just lpp-passage start=1,1 end=100,100

# Find geodesic
just lpp-geodesic

# Check Tracy-Widom
just lpp-verify-tw

# Matrix product ansatz
just lpp-mpa q=0.5
```

## Configuration

```yaml
# last-passage-percolation.yaml
model:
  grid_size: 100
  weight_distribution: exponential  # or geometric, bernoulli
  
analysis:
  compute_geodesics: true
  tracy_widom_test: true
  competition_interface: false

matrix_product:
  q: 0.5
  boundary: stationary
```

## Related Skills

- **kpz-universality** (0): Scaling limit
- **yang-baxter-integrability** (-1): Algebraic structure
- **louisville-quantum-gravity** (+1): Stationary measures
- **colored-vertex-model** (+1): Colored particles
- **gay-mcp** (+1): Deterministic paths

## Research References

1. Johansson (2000): "Shape fluctuations and random matrices"
2. Baik-Deift-Johansson (1999): "On the distribution of the length of the longest increasing subsequence"
3. Ferrari-Spohn (2005): "Scaling limit for the space-time covariance of the stationary TASEP"
4. Corwin (2012): "The Kardar-Parisi-Zhang equation and universality class"

---

**Skill Name**: last-passage-percolation
**Type**: Discrete KPZ Model
**Trit**: 0 (ERGODIC)
**Key Property**: Tracy-Widom fluctuations, geodesic competition
**Status**: ✅ Production Ready

---

## Cat# Integration

```
Trit: 0 (ERGODIC)
Home: DiscreteProb
Poly Op: ⊗
Kan Role: Adj
Color: #20B2AA
```

### Passage Time as Profunctor

```
G: ℤ₊² ↛ ℝ
G(start, end) = max path weight
```

Satisfies semi-group property:
```
G(a, c) = max_b [G(a, b) + G(b, c)]
```

### GF(3) Naturality

```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

## Autopoietic Marginalia

> **Paths compete. Weights accumulate. The maximum emerges.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record geodesic patterns
- **REMEMBERING** (0): Connect to TASEP dynamics
- **WORLDING** (+1): Discover new limit shapes

*Add Interaction Exemplars here as the skill is used.*
