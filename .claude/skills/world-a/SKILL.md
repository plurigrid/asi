---
name: world-a
description: |
  AlgebraicJulia ecosystem: ACSets.jl (attributed C-sets as in-memory algebraic databases),
  Catlab.jl (applied category theory with wiring diagrams and GATs),
  AlgebraicDynamics.jl (compositional dynamical systems via operads),
  Decapodes.jl (discrete exterior calculus for physics simulation),
  CombinatorialSpaces.jl (simplicial sets and DEC meshes),
  GATlab.jl (generalized algebraic theories foundation).
version: 1.0.0
tags:
  - category-theory
  - acsets
  - julia
  - algebraic-julia
  - dynamical-systems
  - physics-simulation
  - wiring-diagrams
color: "#B02825"
hue: 1.5
trit: 1
role: PLUS
wallet: "0x8699edc0960dd5b916074f1e9bd25d86fb416a8decfa46f78ab0af6eaebe9d7a"
neighbors: ["Z", "B"]
mcp_alias: "alice_aptos"
---

# World a: AlgebraicJulia Ecosystem

**Color**: `#B02825` | **Trit**: +1 PLUS | **Hue**: 1.5°

## Wallet

```
0x8699edc0960dd5b916074f1e9bd25d86fb416a8decfa46f78ab0af6eaebe9d7a
```

## GF(3) Role

As a **PLUS (+1)** world, World A serves as a **generator** in triadic operations:
- Generates new solutions
- Executes transformations
- Produces outputs

## Overview

World a contains the core AlgebraicJulia packages—a suite of Julia libraries implementing applied category theory for scientific computing. These packages provide:

- **Categorical databases** as in-memory data structures (ACSets)
- **Compositional modeling** via operads and wiring diagrams
- **Physics simulation** through discrete exterior calculus

## Directory Structure

```
~/worlds/A/
├── ACSets.jl/                    # Attributed C-Sets: algebraic databases
│   ├── src/
│   │   ├── ACSets.jl             # Main module
│   │   ├── ACSetInterface.jl     # Core interface for C-sets
│   │   ├── DenseACSets.jl        # Dense storage implementation
│   │   ├── Schemas.jl            # Schema definitions
│   │   ├── Query.jl              # Query language
│   │   ├── NautyInterface.jl     # Graph isomorphism via nauty
│   │   ├── intertypes/           # Interoperability types
│   │   └── serialization/        # JSON/binary serialization
│   ├── docs/literate/            # Tutorial notebooks
│   └── test/
│
├── Catlab.jl/                    # Applied Category Theory
│   ├── src/
│   │   ├── Catlab.jl             # Main module
│   │   ├── theories/             # GAT definitions (categories, monoidal, etc.)
│   │   ├── categorical_algebra/  # Limits, colimits, functors
│   │   │   ├── cats/             # Category implementations
│   │   │   ├── pointwise/        # C-set categories, data migrations
│   │   │   └── setcats/          # FinSet, SkelFinSet
│   │   ├── wiring_diagrams/      # String diagrams, operads
│   │   ├── graphs/               # Graph types and algorithms
│   │   ├── graphics/             # TikZ, Graphviz, Compose output
│   │   ├── programs/             # Syntax to diagrams
│   │   └── sheaves/              # Sheaf theory
│   ├── docs/literate/
│   │   ├── sketches/
│   │   ├── wiring_diagrams/
│   │   └── graphs/
│   └── benchmark/
│
├── AlgebraicDynamics.jl/         # Compositional Dynamical Systems
│   ├── src/
│   │   ├── AlgebraicDynamics.jl  # Main module
│   │   ├── dwd_dynam.jl          # Directed wiring diagram dynamics
│   │   ├── uwd_dynam.jl          # Undirected wiring diagram dynamics
│   │   ├── cpg_dynam.jl          # Circular port graph dynamics
│   │   └── ThresholdLinear/      # Threshold-linear networks
│   ├── notebooks/springs/        # Spring system examples
│   └── examples/
│
├── Decapodes.jl/                 # Discrete Exterior Calculus PDE Solver
│   ├── src/
│   │   ├── Decapodes.jl          # Main module
│   │   ├── simulation.jl         # ODE/PDE simulation engine
│   │   ├── operators.jl          # DEC operators (d, δ, ⋆, Δ)
│   │   └── canon/                # Canonical forms
│   ├── docs/src/
│   │   ├── fokker_planck/        # Fokker-Planck examples
│   │   ├── navier_stokes/        # Fluid dynamics
│   │   ├── ice_dynamics/         # Glaciology models
│   │   └── climate/              # Climate modeling
│   └── examples/
│       ├── chemistry/
│       ├── climate/
│       └── sw/                   # Shallow water
│
├── CombinatorialSpaces.jl/       # Meshes and Simplicial Sets
│   └── src/
│       ├── SimplicialSets.jl     # Simplicial complex data structures
│       ├── DiscreteExteriorCalculus.jl  # DEC on meshes (82KB!)
│       ├── FastDEC.jl            # Optimized DEC operators
│       ├── CombMeshes.jl         # Combinatorial mesh operations
│       └── Multigrid.jl          # Multigrid solvers
│
├── GATlab.jl/                    # Generalized Algebraic Theories
│   └── src/
│       ├── GATlab.jl             # Main module
│       ├── syntax/               # Term rewriting, parsing
│       ├── models/               # Model implementations
│       ├── stdlib/               # Standard library theories
│       └── nonstdlib/            # Extended theories
│
├── a-tractor/                    # Infrastructure tooling
│   ├── connectome.sh/
│   ├── sshx/                     # SSH multiplexer (Rust+Svelte)
│   └── omega-interractor/
│
├── awesomeDAO/                   # DAO tooling
├── A-F-X-M/                      # Cross-world connections
└── akian.md                      # Marianne Akian (tropical spectrahedra)
```

## Key Packages

### ACSets.jl — Algebraic Databases

**What:** Attributed C-Sets generalize graphs, relational databases, and labeled data structures into a unified categorical framework.

**Key concepts:**
- **Schema**: Defines objects (tables), morphisms (foreign keys), attributes
- **ACSet**: Instance of a schema with data
- **Queries**: Conjunctive queries via `@acset_colim`

```julia
using ACSets

# Define a graph schema
@present SchGraph(FreeSchema) begin
  V::Ob; E::Ob
  src::Hom(E,V); tgt::Hom(E,V)
end

# Create an instance
const Graph = ACSetType(SchGraph)
g = Graph()
add_parts!(g, :V, 3)
add_parts!(g, :E, 2, src=[1,2], tgt=[2,3])
```

### Catlab.jl — Category Theory

**What:** Core library for applied category theory with GATs, functors, limits/colimits, and string diagrams.

**Key modules:**
- `Theories`: Category, MonoidalCategory, Hypergraph, etc.
- `CategoricalAlgebra`: Limits, pushouts, data migration
- `WiringDiagrams`: Operadic composition, string diagrams
- `Graphics`: TikZ, Graphviz visualization

```julia
using Catlab, Catlab.WiringDiagrams

# Compose morphisms as diagrams
f = Hom(:f, [:A], [:B])
g = Hom(:g, [:B], [:C])
compose(f, g)  # f ⋅ g : A → C
```

### AlgebraicDynamics.jl — Compositional Systems

**What:** Build dynamical systems compositionally using wiring diagrams.

**Key types:**
- `ContinuousMachine`: ODE systems with typed ports
- `DiscreteMachine`: Discrete-time systems
- `UWD`: Undirected wiring diagrams for composition

```julia
using AlgebraicDynamics.UWDDynam

# Define component systems, compose via wiring diagrams
# Ports declare interfaces, wiring diagram composes systems
```

### Decapodes.jl — Physics Simulation

**What:** Solve PDEs on meshes using discrete exterior calculus. Physics equations become wiring diagrams.

**Key features:**
- DEC operators: exterior derivative `d`, Hodge star `⋆`, codifferential `δ`
- Automatic code generation from diagram specifications
- GPU acceleration support

```julia
using Decapodes

# Diffusion equation: ∂u/∂t = Δu
@decapode Diffusion begin
  u::Form0
  ∂ₜ(u) == Δ(u)
end
```

### CombinatorialSpaces.jl — Meshes

**What:** Simplicial sets and DEC infrastructure for Decapodes.

**Key types:**
- `EmbeddedDeltaSet2D`: 2D triangular meshes
- `EmbeddedDeltaDualComplex2D`: Dual meshes for DEC

### GATlab.jl — GAT Foundation

**What:** Generalized Algebraic Theories as the type-theoretic foundation for Catlab.

## Usage Patterns

### Pattern 1: Define Schema → Create Instances → Query

```julia
using ACSets, Catlab

# 1. Define schema
@present SchPetri(FreeSchema) begin
  S::Ob; T::Ob; I::Ob; O::Ob
  is::Hom(I,S); it::Hom(I,T)
  os::Hom(O,S); ot::Hom(O,T)
end

# 2. Create instance
PetriNet = ACSetType(SchPetri)
sir = PetriNet()

# 3. Query for patterns
@acset_colim sir pat begin
  # conjunctive query
end
```

### Pattern 2: Wiring Diagram → Dynamical System

```julia
using AlgebraicDynamics, Catlab.WiringDiagrams

# 1. Define component machines
m1 = ContinuousMachine(1, 1, (x,p,t) -> [...])
m2 = ContinuousMachine(1, 1, (x,p,t) -> [...])

# 2. Wire together
d = WiringDiagram(...)
add_boxes!(d, [m1, m2])

# 3. Compose and simulate
system = oapply(d, [m1, m2])
```

### Pattern 3: Decapode → Simulation

```julia
using Decapodes, CombinatorialSpaces

# 1. Define physics
@decapode Heat begin
  u::Form0
  ∂ₜ(u) == α * Δ(u)
end

# 2. Load/create mesh
mesh = loadmesh("domain.obj")
dualmesh = EmbeddedDeltaDualComplex2D(mesh)

# 3. Generate and run simulation
sim = eval(gensim(Heat))
```

## Cross-Package Integration

```
GATlab.jl (GATs, syntax)
    ↓
Catlab.jl (categories, wiring diagrams)
    ↓
ACSets.jl (data storage)
    ↓
AlgebraicDynamics.jl + CombinatorialSpaces.jl
    ↓
Decapodes.jl (physics simulation)
```

## Key Files Reference

| Package | File | Purpose |
|---------|------|---------|
| ACSets | `DenseACSets.jl` | Main ACSet implementation |
| ACSets | `Schemas.jl` | `@present` macro for schemas |
| Catlab | `theories/` | All GAT definitions |
| Catlab | `wiring_diagrams/` | String diagram DSL |
| AlgDyn | `dwd_dynam.jl` | Directed composition |
| AlgDyn | `uwd_dynam.jl` | Undirected composition |
| Decapodes | `simulation.jl` | PDE solver core |
| CombSpaces | `DiscreteExteriorCalculus.jl` | DEC operators |

## Related Worlds

- **World a**: Formal methods (verification of categorical constructions)
- **World a**: Experimental extensions
- **World a**: Mathematical foundations

## External Resources

- [AlgebraicJulia Docs](https://algebraicjulia.org/)
- [Catlab.jl Tutorial](https://algebraicjulia.github.io/Catlab.jl/stable/)
- [Decapodes Paper](https://arxiv.org/abs/2401.07759)
