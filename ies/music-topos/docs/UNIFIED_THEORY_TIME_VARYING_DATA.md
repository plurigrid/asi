# Unified Theory of Time-Varying Data

**Date**: 2025-12-22
**Status**: Theoretical Synthesis
**Core Insight**: All time-varying data analysis is sheaf cohomology on temporal shapes

---

## The Grand Unification

```
                     ┌─────────────────────────────────────────┐
                     │    UNIFIED THEORY OF TIME-VARYING DATA  │
                     └─────────────────────────────────────────┘
                                        │
            ┌───────────────────────────┼───────────────────────────┐
            ▼                           ▼                           ▼
    ┌───────────────┐          ┌───────────────┐          ┌───────────────┐
    │ DECOMPOSITION │          │  COMPOSITION  │          │   LEARNING    │
    │   (Analysis)  │          │  (Synthesis)  │          │  (Inference)  │
    └───────────────┘          └───────────────┘          └───────────────┘
            │                           │                           │
    ┌───────┴───────┐          ┌───────┴───────┐          ┌───────┴───────┐
    │ DMD           │          │ AlgebraicDyn  │          │ Sheaf NN      │
    │ StructuredDec │          │ Operads       │          │ Koopman       │
    │ Koopman       │          │ Wiring Diag   │          │ GFlowNet      │
    └───────────────┘          └───────────────┘          └───────────────┘
            │                           │                           │
            └───────────────────────────┼───────────────────────────┘
                                        ▼
                            ┌─────────────────────┐
                            │  SHEAVES ON SHAPES  │
                            │   F: Shape^op → C   │
                            └─────────────────────┘
```

---

## 1. The Categorical Foundation

### Three Equivalent Descriptions of Dynamics (Das & Suda 2025)

Every dynamical system can be described equivalently as:

1. **Semigroup Action**: `T × X → X` (time acts on state)
2. **Parameterized Endomorphisms**: `T → End(X)` (time indexes transformations)  
3. **Enriched Functor**: `BT → V-Cat` (time as enriching category)

These are unified by **enriched functor theory**:

```
Time (semigroup T)  ──enriched functor──▶  State space X
        │                                        │
        ▼                                        ▼
   Monoidal category                     V-enriched category
   (composition = +)                    (homs = transitions)
```

### Machines as Sheaves (Schultz-Spivak-Vasilakopoulou 2016)

The foundational paper "Dynamical Systems and Sheaves" establishes:

> **Machines** (input-output systems through time) = **Sheaves on temporal sites**

A machine M with inputs I and outputs O is a sheaf:
```
M: Interval^op → Set
M(t) = { behaviors on interval t }
```

Composition via **lax monoidal functors** ensures:
- Subsystems compose correctly
- Time glues coherently (sheaf condition)
- Determinism/totality propagate compositionally

---

## 2. The Shape-Target Duality

### Universal Pattern

| Framework | Shape Category | Target Category | Object Type |
|-----------|---------------|-----------------|-------------|
| **DMD** | [m] (linear order) | Vect | Snapshots |
| **StructuredDecomp** | Tree T | Graph | Subgraphs |
| **AlgebraicDynamics** | Operad O | ODE/DDE | Machines |
| **Sheaf NN** | Graph G | Vect | Node features |
| **Koopman** | ℕ or ℝ⁺ | L²(X) | Observables |

All are instances of:
```
Presheaf F: Shape^op → Target
Global object = colim(F)
Local computation = per-object evaluation
Gluing = morphism compatibility
Error = H¹(Shape, F) ≠ 0
```

### The Colimit Reconstruction Theorem

**Theorem**: For any structured decomposition d: ∫Shape → C, the original object is:
```
X = colim(d) = ∫^{s ∈ Shape} d(s)
```

**Corollary** (DMD): The dynamics matrix A is the colimit of the snapshot diagram.

**Corollary** (StructuredDecomp): The graph G is the colimit of the bag diagram.

---

## 3. Compositional Dynamics (AlgebraicDynamics.jl)

### Operads as Composition Patterns

```
UNDIRECTED (Resource Sharers)     DIRECTED (Machines)
─────────────────────────────     ────────────────────
    Shared state                     Signal flow
    Junctions                        Wires
    oapply via pushout               oapply via composition
    
    ∐ states                         ∐ states
       │                                │
    pushout (identify ports)        compose (wire outputs→inputs)
       │                                │
    ▼                               ▼
    Composite dynamics              Composite machine
```

### The oapply Functor

```julia
oapply: WiringDiagram × [Components] → CompositeSystem
```

This is an **operad algebra evaluation**:
- Operad O = wiring diagram structure
- Algebra A = dynamical systems
- oapply implements the algebra structure map

---

## 4. Sheaf Neural Networks for Time-Varying Data

### The Sheaf Laplacian (Bodnar et al. 2022)

A sheaf F on graph G assigns:
- Vector space F(v) to each node v
- Linear map F(e): F(u) → F(v) for edge e: u → v

The **sheaf Laplacian** L_F generalizes the graph Laplacian:
```
(L_F x)_v = Σ_{e: u→v} F(e)^T F(e) (x_v - F(e) x_u)
```

### Sheaf Diffusion for Dynamics

Time-varying node features evolve via:
```
dx/dt = -L_F x
```

**Key insight**: The restriction maps F(e) encode how dynamics transform across edges.

For heterogeneous time series (different sensors, different dynamics):
- F(v) = local state space
- F(e) = synchronization/coupling map
- L_F captures coupled dynamics

---

## 5. Koopman Operators: Infinite-Dimensional Lifting

### The Koopman Framework

For dynamics `x_{t+1} = f(x_t)`, the Koopman operator K acts on observables:
```
(Kg)(x) = g(f(x))
```

**Key property**: K is **linear** even when f is nonlinear.

### DMD as Finite Koopman Approximation

DMD finds the best rank-r approximation:
```
K ≈ Φ Λ Φ^†
```

Where:
- Φ = DMD modes (approximate Koopman eigenfunctions)
- Λ = eigenvalues (dynamics)

### Categorical Interpretation

Koopman operator = **pushforward functor** on observable sheaves:
```
f_*: Sh(X) → Sh(X)
(f_* F)(U) = F(f^{-1}(U))
```

---

## 6. The Unified Framework

### Time-Varying Data as Presheaves on Interval Categories

Let **Int** = category of intervals with inclusions.

**Definition**: A **time-varying dataset** is a presheaf:
```
D: Int^op → Set (or Vect, Graph, etc.)
D([t₁,t₂]) = data observable on interval [t₁,t₂]
```

**Restriction maps** capture how data restricts to subintervals.

### Decomposition Methods as Kan Extensions

**DMD**: Right Kan extension along forgetful functor
```
[m] ──forget──▶ {*}
 │                │
 D               Ran_F(D) = "average dynamics"
 ▼                ▼
Vect             Vect
```

**StructuredDecomp**: Left Kan extension along tree embedding
```
∫T ──embed──▶ Graph
 │              │
 d             Lan(d) = colim(d) = original graph
 ▼              ▼
Graph          Graph
```

### Error as Sheaf Cohomology

**H⁰(Shape, F)** = Global sections = consistent solutions
**H¹(Shape, F)** = Obstructions = reconstruction error

| Method | H¹ = 0 means | H¹ ≠ 0 means |
|--------|--------------|--------------|
| DMD | Perfect reconstruction | Residual error |
| StructuredDecomp | Solution exists | No global solution |
| Sheaf NN | No oversmoothing | Information loss |
| Koopman | Exact lifting | Closure error |

---

## 7. Implementation Architecture

### The Unified Stack

```
┌─────────────────────────────────────────────────────────────────┐
│  Layer 6: Applications                                          │
│  Music analysis, fluid dynamics, neural data, finance           │
├─────────────────────────────────────────────────────────────────┤
│  Layer 5: Learning                                              │
│  Sheaf NN, GFlowNet, Forward-Forward, Koopman learning         │
├─────────────────────────────────────────────────────────────────┤
│  Layer 4: Decomposition                                         │
│  DMD, StructuredDecomp, SVD, wavelets                          │
├─────────────────────────────────────────────────────────────────┤
│  Layer 3: Composition                                           │
│  AlgebraicDynamics, operads, wiring diagrams                   │
├─────────────────────────────────────────────────────────────────┤
│  Layer 2: Sheaves                                               │
│  Presheaves, colimits, Kan extensions, cohomology              │
├─────────────────────────────────────────────────────────────────┤
│  Layer 1: Categories                                            │
│  Catlab, ACSets, enriched functors                             │
└─────────────────────────────────────────────────────────────────┘
```

### Julia Implementation Sketch

```julia
module UnifiedTimeVarying

using Catlab, AlgebraicDynamics, StructuredDecompositions

# A time-varying dataset is a presheaf on intervals
abstract type TimeVaryingData{T} end

# Shape categories
abstract type TemporalShape end
struct LinearOrder <: TemporalShape; n::Int; end
struct TreeShape <: TemporalShape; tree::Graph; end
struct OperadShape <: TemporalShape; operad::Any; end

# The universal decomposition type
struct Decomposition{S<:TemporalShape, C, F}
    shape::S                    # The shape category
    diagram::F                  # Functor shape → C
    target::Type{C}            # Target category
end

# DMD is a decomposition with linear shape and Vect target
function dmd_decomposition(snapshots::Matrix)
    shape = LinearOrder(size(snapshots, 2))
    diagram = i -> snapshots[:, i]  # Simplified
    Decomposition(shape, diagram, Vector)
end

# StructuredDecomp is a decomposition with tree shape and Graph target
function structured_decomposition(g::Graph)
    tree = compute_tree_decomposition(g)
    shape = TreeShape(tree)
    diagram = v -> induced_subgraph(g, bag(tree, v))
    Decomposition(shape, diagram, Graph)
end

# Composition via AlgebraicDynamics
function compose_dynamics(pattern::WiringDiagram, components::Vector{Machine})
    oapply(pattern, components)
end

# Cohomology measures error
function cohomology(d::Decomposition)
    # H⁰ = global sections
    # H¹ = obstructions
    # ... (Čech cohomology computation)
end

# Reconstruct original from decomposition
function reconstruct(d::Decomposition)
    colimit(d.diagram)
end

end
```

---

## 8. GF(3) Triads for Time-Varying Data

```
# Decomposition Triad
DMD (-1, spectral validator)
    ⊗ StructuredDecomp (0, categorical coordinator)
    ⊗ Koopman (+1, infinite-dim generator)
    = 0 ✓

# Composition Triad
ResourceSharer (-1, undirected validator)
    ⊗ WiringDiagram (0, pattern coordinator)
    ⊗ Machine (+1, directed generator)
    = 0 ✓

# Learning Triad
SheafNN (-1, geometric validator)
    ⊗ GFlowNet (0, sampling coordinator)
    ⊗ Koopman-Learning (+1, dynamics generator)
    = 0 ✓
```

---

## 9. Key Papers

| Paper | Authors | Contribution |
|-------|---------|--------------|
| **Dynamical Systems and Sheaves** (2016) | Schultz, Spivak, Vasilakopoulou | Sheaf theory for machines |
| **Dynamical Systems as Enriched Functors** (2025) | Das, Suda | Three equivalent descriptions |
| **Neural Sheaf Diffusion** (2022) | Bodnar et al. | Sheaf Laplacian for GNNs |
| **Structured Decompositions** (2023) | Bumpus, Fairbanks | FPT via sheaves on trees |
| **Modern Koopman Theory** (2021) | Brunton et al. | Data-driven operator learning |
| **Compositional Deep Learning** (2019) | Gavranović | Functorial neural networks |
| **AlgebraicDynamics.jl** (2020) | Libkind et al. | Operad algebras for ODEs |

---

## 10. The Punchline

> **All time-varying data analysis is sheaf theory on temporal shapes.**
>
> - **Decomposition** = finding a good shape and presheaf
> - **Composition** = operad algebra on wiring diagrams
> - **Learning** = finding restriction maps (sheaf structure)
> - **Error** = sheaf cohomology obstruction
> - **Reconstruction** = colimit of the diagram

The differences between DMD, tree decompositions, and neural networks are merely:
1. **Shape category** (linear, tree, graph, operad)
2. **Target category** (Vect, Graph, Hilbert space)
3. **Optimization method** (SVD, SAT, gradient descent)

**Same categorical structure. Different instantiations.**

---

## 11. Next Steps

1. **Implement** `UnifiedTimeVarying.jl` bridging StructuredDecompositions + DMD
2. **Prove** DMD = right Kan extension theorem formally
3. **Connect** to music-topos: musical time as presheaf on interval category
4. **Benchmark** against PyDMD on fluid dynamics data
5. **Extend** to delay systems via sheaves on temporal sites with history

---

## References

1. Schultz, Spivak, Vasilakopoulou (2019) "Dynamical Systems and Sheaves" - Applied Categorical Structures
2. Das, Suda (2025) "Dynamical Systems as Enriched Functors" - arXiv:2509.05900
3. Bumpus et al. (2023) "Structured Decompositions" - arXiv:2207.06091
4. Bodnar et al. (2022) "Neural Sheaf Diffusion" - arXiv:2202.04579
5. Brunton et al. (2021) "Modern Koopman Theory" - SIAM Review
6. Libkind (2020) "An Algebra of Resource Sharers" - arXiv:2007.14442
7. Gavranović (2019) "Compositional Deep Learning" - arXiv:1907.08292
