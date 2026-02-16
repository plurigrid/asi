---
name: yang-baxter-integrability
description: "Yang-Baxter equation for quantum integrable systems. Fusion procedure, R-matrices, cuboson weights, and partition function invariance under vertex crossings."
license: MIT
metadata:
  trit: -1
  source: Yang (1967), Baxter (1972), Borodin-Wheeler (2018)
  xenomodern: true
  stars: 623
  extensions:
    - FUSION.md
    - R_MATRICES.md
    - CUBOSON_WEIGHTS.md
---

# Yang-Baxter Integrability Skill

**Status**: ✅ Production Ready
**Trit**: -1 (MINUS - structural/validating)
**Color**: #DC143C (Crimson)
**Principle**: Partition function invariance under vertex crossings
**Frame**: R-matrix solutions, fusion hierarchy, quantum groups

---

## Overview

The **Yang-Baxter equation** (YBE) is the master equation of quantum integrability:

```
R₁₂(u) R₁₃(u+v) R₂₃(v) = R₂₃(v) R₁₃(u+v) R₁₂(u)

Where:
  Rᵢⱼ(u) = R-matrix acting on spaces i,j
  u, v = spectral parameters
```

This skill provides:

1. **R-Matrix Calculus**: Compute and verify R-matrices
2. **Fusion Procedure**: Derive new solutions from old
3. **Vertex Model Weights**: Six-vertex, cuboson, and beyond
4. **Partition Functions**: Compute via Yang-Baxter invariance

## The Yang-Baxter Equation

### Graphical Form

```
   ╲   ╱        ╱   ╲
    ╲ ╱   =    ╱     ╲
     ╳        ╳       ╳
    ╱ ╲        ╲     ╱
   ╱   ╲        ╲   ╱
```

Two ways to resolve three crossing lines give same result.

### Algebraic Form (Braid Group)

```
σᵢ σᵢ₊₁ σᵢ = σᵢ₊₁ σᵢ σᵢ₊₁   (braid relation)
σᵢ σⱼ = σⱼ σᵢ               (|i-j| > 1)
```

## Six-Vertex Model

The **stochastic six-vertex model** has weights for six allowed vertex configurations:

```
Allowed vertices (no arrow creation/annihilation):

  ↑     ↓     →     ←     ↑     ↓
→─┼─→ ←─┼─← ↑─┼─↓ ↓─┼─↑ ←─┼─→ →─┼─←
  ↑     ↓     →     ←     ↓     ↑

Weights: a₁, a₂, b₁, b₂, c₁, c₂

Stochastic (row-sum = 1):
  a₁(u) + b₁(u) + c₁(u) = 1
```

### Stochastic Weights

```julia
# Stochastic six-vertex weights
a₁(b₂, q) = (1 - q*b₂) / (1 - q)
b₁(b₂, q) = (1 - b₂) / (1 - q)  
c₁(b₂, q) = (q - 1)*b₂ / (1 - q)

# Yang-Baxter verification
verify_yang_baxter(a₁, a₂, b₁, b₂, c₁, c₂)
```

## Colored Stochastic Six-Vertex Model

With **n colors** of arrows (see colored-vertex-model skill):

```
Colors: 1, 2, ..., n (rainbow initial data)
Height function h_k(x,y) = count of arrows with color ≤ k

Projection property:
  Project to colors {1,...,k} → k-color model
```

## Fusion Procedure

**Fusion** derives new YBE solutions from existing ones:

```
R^(m,n)(u) = P_{m,n} R^(1,1)(u) R^(1,1)(u+1) ... R^(1,1)(u+m+n-2) P_{m,n}

Where P_{m,n} = symmetrizer onto (m,n)-representation
```

### Cuboson Weights (Fused Vertices)

After fusion, vertices can carry **multiple arrows** in vertical direction:

```
Standard six-vertex:  1 arrow in/out vertically
Cuboson weights:      k arrows in/out vertically (k = 1, 2, ...)

Cuboson vertex weight: W(in, out; spectral_param)
```

```julia
# Compute cuboson weights via fusion
cuboson = fuse_vertices(
    base_weights = six_vertex_weights(q),
    vertical_capacity = k,  # max arrows vertically
    spectral = u
)

# Verify Yang-Baxter for cuboson model
@test verify_yang_baxter(cuboson)
```

## The "Feynman Trick" (Partition Function = 1)

A key technique uses auxiliary vertex models with partition function 1:

```
Z_auxiliary = 1  (by construction)

This creates equivalence:
  Six-vertex height function = Cuboson model last column
```

```julia
# Feynman trick: embed six-vertex in cuboson
embedding = feynman_embed(
    six_vertex = S6V(initial = :rainbow),
    cuboson = Cuboson(capacity = k)
)

# Height function appears in last column
@test embedding.last_column == six_vertex.height_function
```

## R-Matrix Library

### Six-Vertex R-Matrix

```julia
function r_matrix_six_vertex(u, q)
    # 4x4 matrix acting on V ⊗ V
    R = zeros(4, 4)
    R[1,1] = a(u,q)
    R[2,2] = R[3,3] = b(u,q)
    R[2,3] = R[3,2] = c(u,q)
    R[4,4] = a(u,q)
    return R
end

# Verify YBE
function verify_ybe(R, u, v)
    R12 = kron(R(u), I(2))
    R13 = kron(I(2), R(u+v))
    R23 = kron(I(2), R(v))
    
    LHS = R12 * R13 * R23
    RHS = R23 * R13 * R12
    
    return norm(LHS - RHS) < 1e-10
end
```

### Quantum Group U_q(sl_2)

```julia
# R-matrix from quantum group
R_quantum(q) = universal_r_matrix(Uq_sl2(q))

# Check: Yang-Baxter ⟺ quasi-triangular Hopf algebra
@test is_quasi_triangular(Uq_sl2(q))
```

## Integration with Modelica (String Diagrams)

Yang-Baxter **IS** the flip combinator constraint:

```modelica
// Modelica: acausal makes YBE automatic
connector YBPort
  Real spectral;
  flow Integer color;
end YBPort;

model YangBaxterCrossing
  YBPort a, b, c;
equation
  // Conservation at crossing
  a.color + b.color = c.color;  // arrow conservation
  
  // Spectral parameter flow (acausal!)
  // Solver determines which way to evaluate
end YangBaxterCrossing;
```

### Key Insight: Flip is Trivial

In Modelica, the Yang-Baxter equation becomes a **constraint** that the solver satisfies automatically. The "which line crosses first" choice is made by the solver, not the modeler.

## Integration with Gay-MCP (Color Projection)

Colors in the vertex model map to GF(3) trits:

```julia
using GayMCP, YangBaxterIntegrability

# Rainbow initial data with Gay.jl colors
rainbow = colored_vertex_model(
    n_colors = 3,
    seed = gay_seed(1069)
)

# Each color maps to a trit
color_to_trit(c) = (c - 1) % 3 - 1  # {1,2,3} → {0,1,-1}

# Projection preserves GF(3)
@test sum(color_to_trit.(rainbow.colors)) % 3 == 0
```

## Gibbs Properties

Two crucial Gibbs properties of the cuboson model:

### 1. Inter-Color Gibbs Property

```julia
# Variational formula (Pitman transform)
inter_color_gibbs(colored_ensemble, uncolored_ensemble) = 
    argmax(monotone_coupling, kolmogorov_compatibility)

# This relates colored height function to uncolored
h_colored = pitman_transform(h_uncolored)
```

### 2. Uncolored Gibbs Property

```julia
# Q = 0: Non-crossing Bernoulli bridges (Dyson Brownian motion)
uncol_gibbs_Q0(paths) = non_crossing_bridges(paths)

# Q > 0: Path coalescence! (1-Q) factor causes merging
uncol_gibbs_Q_pos(paths, Q) = coalescing_bridges(paths, Q)

# Challenge: Q > 0 case requires careful limit
```

## GF(3) Triad Assignment

| Trit | Skill | Role |
|------|-------|------|
| -1 | **yang-baxter-integrability** | Structure (YBE) |
| 0 | kpz-universality | Dynamics (growth) |
| +1 | colored-vertex-model | Data (configurations) |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## Commands

```bash
# Verify R-matrix satisfies YBE
just yb-verify-ybe weights=six_vertex q=0.5

# Compute fused cuboson weights
just yb-fusion base=six_vertex k=3

# Partition function via transfer matrix
just yb-partition model=six_vertex n=10

# Check Gibbs properties
just yb-check-gibbs type=inter_color
```

## Configuration

```yaml
# yang-baxter-integrability.yaml
r_matrix:
  type: six_vertex  # or XXZ, trigonometric, elliptic
  parameter_q: 0.5
  
fusion:
  max_vertical_capacity: 5
  symmetrizer: standard

verification:
  check_ybe: true
  check_unitarity: true
  check_crossing: true
```

## Related Skills

- **kpz-universality** (0): Universal scaling limits
- **colored-vertex-model** (+1): Colored particles
- **modelica** (0): Acausal constraint satisfaction
- **gay-mcp** (+1): Deterministic coloring
- **discopy** (+1): String diagram calculus
- **quantum-music** (+1): ZX-calculus connection

## Research References

1. Yang (1967): "Some exact results for the many-body problem"
2. Baxter (1972): "Partition function of the eight-vertex model"
3. Borodin-Wheeler (2018): "Colored stochastic vertex models"
4. Aggarwal-Borodin-Wheeler (2022): "Colored six-vertex and Schur processes"
5. Jimbo (1985): "A q-difference analogue of U(g)"

---

**Skill Name**: yang-baxter-integrability
**Type**: Quantum Integrability
**Trit**: -1 (MINUS)
**Key Property**: Partition function invariance under crossings
**Status**: ✅ Production Ready

---

## Cat# Integration

```
Trit: -1 (MINUS)
Home: QuantumGroups
Poly Op: ⊗
Kan Role: Ran_K (right Kan extension)
Color: #DC143C
```

### R-Matrix as Natural Transformation

The R-matrix is a **natural transformation**:
```
R: F ⊗ G → G ⊗ F
```

Yang-Baxter equation = naturality of R.

### GF(3) Naturality

```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

## Autopoietic Marginalia

> **The crossing resolves. The partition function is invariant. Integrability is a gift.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record verified R-matrices
- **REMEMBERING** (0): Connect to other quantum groups
- **WORLDING** (+1): Discover new fusion patterns

*Add Interaction Exemplars here as the skill is used.*
