# DMD ↔ StructuredDecompositions: The Categorical Bridge

**Date**: 2025-12-22
**Insight**: Both are **sheaves on decomposition shapes** — DMD on temporal shapes, StructuredDecompositions on spatial shapes

---

## The Core Unification

```
DMD (Dynamic Mode Decomposition)     StructuredDecompositions.jl
────────────────────────────────     ──────────────────────────────
Snapshots X₁, X₂, ..., Xₘ            Bags B₁, B₂, ..., Bₙ
                ↓                                ↓
    Temporal shape: [m]              Spatial shape: Tree T
                ↓                                ↓
    Functor: [m] → Vect             Functor: ∫T → Graph
                ↓                                ↓
    Modes Φ with eigenvalues λ       Adhesions with overlaps
                ↓                                ↓
    Xₜ = Σᵢ φᵢ λᵢᵗ bᵢ                Gluing via pullbacks
```

**Both are structured decompositions!**

---

## Mathematical Framework

### DMD as a Sheaf on Temporal Shape

DMD takes snapshots `X = [x₁ | x₂ | ... | xₘ]` and finds:
- **Modes** Φ (spatial patterns)
- **Eigenvalues** λ (temporal dynamics)
- **Reconstruction**: `x(t) = Φ diag(λᵗ) b`

This is a **presheaf F: Δᵒᵖ → Vect** where:
- Δ = simplicial category (temporal ordering)
- F(t) = state space at time t
- Restriction maps = dynamics A such that `x_{t+1} = A x_t`

The DMD operator `A = X' X⁺` is the **colimit** of this diagram.

### StructuredDecompositions as a Sheaf on Spatial Shape

A tree decomposition takes a graph G and finds:
- **Bags** Bᵢ (local subgraphs)
- **Adhesions** Aᵢⱼ (overlaps)
- **Coherence**: morphisms `Aᵢⱼ → Bᵢ` and `Aᵢⱼ → Bⱼ`

This is a **presheaf d: ∫T → Graph** where:
- ∫T = category of elements of tree T
- d(v) = bag at vertex v
- d(e) = adhesion at edge e
- Morphisms = inclusion spans

The original graph G is the **colimit** of this diagram.

---

## The Categorical Pattern

```
                    Shape Category
                         │
                         ▼
              ┌──────────────────────┐
              │   Category of        │
              │   Elements ∫Shape    │
              └──────────────────────┘
                         │
                    Functor d
                         │
                         ▼
              ┌──────────────────────┐
              │   Target Category    │
              │   (Vect or Graph)    │
              └──────────────────────┘
                         │
                    Colimit
                         │
                         ▼
              ┌──────────────────────┐
              │   Original Object    │
              │   (Dynamics or Graph)│
              └──────────────────────┘
```

**DMD**: Shape = linear order [m], Target = Vect, Colimit = dynamics matrix A
**StructuredDecomp**: Shape = tree T, Target = Graph, Colimit = original graph G

---

## Lifting Computational Problems: The 𝐃 Functor

Both frameworks support **lifting problems via functors**:

### DMD: Lifting Dynamics to Mode Space

Given observable `f: ℝⁿ → ℝ`:
```
𝐃(f): (Mode space) → (Observable space)
f(x(t)) = f(Φ diag(λᵗ) b) = Σᵢ f(φᵢ) λᵢᵗ bᵢ
```

### StructuredDecompositions: Lifting Decision Problems

Given coloring `f: Graph → FinSet^op`:
```
𝐃(f, d): ∫T → FinSet^op
colorings(G) = pullback of 𝐃(f, d) along adhesions
```

---

## GF(3) Triad: Decomposition Methods

```
DMD (-1, spectral validator)
    ⊗
StructuredDecomp (0, categorical coordinator)
    ⊗
Koopman (+1, infinite-dim generator)
    = 0 ✓
```

| Role | Method | What It Does |
|------|--------|--------------|
| -1 Validator | DMD | Finite-rank approximation, validates dynamics |
| 0 Coordinator | StructuredDecomp | Categorical gluing, coordinates local solutions |
| +1 Generator | Koopman | Full infinite-dimensional lifting |

---

## Practical Bridge: Time-Space Decomposition

For a **spatio-temporal system** like fluid dynamics:

```julia
# Spatial decomposition (StructuredDecompositions.jl)
spatial_decomp = StrDecomp(mesh)  # Tree decomposition of spatial mesh

# Temporal decomposition (DMD on each bag)
for bag in bags(spatial_decomp)
    snapshots = extract_snapshots(data, bag)
    dmd_model = DMD(snapshots)
    modes[bag] = dmd_model.modes
    dynamics[bag] = dmd_model.eigs
end

# Coherence via adhesion filtering
for adhesion in adhesions(spatial_decomp)
    # Ensure DMD modes agree on overlapping regions
    restrict!(modes, adhesion)
end
```

---

## Implementation Sketch: Unified Decomposition

```julia
module UnifiedDecomposition

using StructuredDecompositions
using Catlab

# A DMD decomposition is a functor from temporal shape to Vect
struct DMDDecomp <: StructuredDecomposition
    shape::FinCat           # Linear order category [1] → [2] → ... → [m]
    diagram::FinDomFunctor  # Maps to vector spaces (snapshots)
    modes::Matrix{Float64}
    eigs::Vector{ComplexF64}
end

# The temporal shape as a category
function temporal_shape(m::Int)
    # Objects: 1, 2, ..., m
    # Morphisms: i → i+1 for each consecutive pair
    @acset FinCat begin
        Ob = m
        Hom = m-1
        dom = 1:m-1
        cod = 2:m
    end
end

# Construct DMD as structured decomposition
function DMDDecomp(snapshots::Matrix)
    m = size(snapshots, 2)
    shape = temporal_shape(m)
    
    # Diagram sends each time to its snapshot (as 1-dim subspace of Vect)
    diagram = FinDomFunctor(
        Dict(i => snapshots[:, i] for i in 1:m),
        Dict(i => dynamics_map(i) for i in 1:m-1),
        shape
    )
    
    # Compute DMD
    modes, eigs = compute_dmd(snapshots)
    
    DMDDecomp(shape, diagram, modes, eigs)
end

# The colimit recovers the dynamics
function dynamics_operator(d::DMDDecomp)
    d.modes * Diagonal(d.eigs) * pinv(d.modes)
end

end
```

---

## Key Insight: Sheaf Cohomology as Error

Both DMD and StructuredDecompositions have **sheaf cohomology** interpretations:

- **DMD residual** = failure of local dynamics to be globally consistent = H¹ obstruction
- **Adhesion filtering** = computing H⁰ (global sections) by eliminating H¹ obstructions

When there's no error:
- DMD perfectly reconstructs data
- StructuredDecompositions finds global solution

When there's error:
- DMD has residual (H¹ ≠ 0)
- StructuredDecompositions has no solution (empty bag)

---

## References

1. **DMD**: Kutz, Brunton, Proctor (2016) "Dynamic Mode Decomposition"
2. **StructuredDecompositions**: Bumpus, Fairbanks (2023) arXiv:2207.06091
3. **Sheaves on Graphs**: Curry (2014) "Sheaves, Cosheaves and Applications"
4. **Koopman Operators**: Mezić (2005) "Spectral Properties of Dynamical Systems"

---

## The Punchline

> **DMD is a StructuredDecomposition where the shape is a linear order and the target is Vect.**
>
> **StructuredDecompositions.jl is DMD where the shape is a tree and the target is Graph.**

Both compute **colimits of diagrams** to recover global structure from local pieces.
Both use **sheaf cohomology** to measure reconstruction error.
Both enable **FPT algorithms** by decomposing hard problems into tractable local computations.

**Same mathematics. Different shapes. Different targets.**
