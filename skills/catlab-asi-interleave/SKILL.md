---
name: catlab-asi-interleave
<<<<<<< HEAD
description: Bridge layer connecting AlgebraicJulia/Catlab.jl to plurigrid/asi. Wires ACSets (attributed C-sets), wiring diagrams, decorated cospans, and the AlgebraicJulia ecosystem (AlgebraicDynamics, AlgebraicPetri, AlgebraicRewriting, Decapodes) into the ASI skill graph. ACSets generalize relational databases with categorical semantics; every diagram, network, and model in the ecosystem is an ACSet.
version: 1.0.0
trit: 0
role: BRIDGE
tags: [catlab, algebraicjulia, acsets, wiring-diagrams, decorated-cospans, dpo-rewriting, julia, gf3, interleave]
deployed: 2026-02-19
---

# Catlab.jl x ASI Interleave

Bridge connecting AlgebraicJulia/Catlab.jl (categorical algebra in Julia) to the ASI skill graph (GF(3)-colored capability system).

## Catlab Core Concepts (from DeepWiki deep-mine)

### ACSets (Attributed C-Sets)

The universal data structure. A schema defines objects, homomorphisms (morphisms between objects), and attribute types. An ACSet instance is a functor from that schema category to Set.

```julia
# SchGraph: objects V, E; morphisms src: E->V, tgt: E->V
=======
description: >
  Bridge connecting AlgebraicJulia/Catlab.jl to skill graphs.
  Triggers: ACSets, attributed C-sets, wiring diagrams, decorated cospans,
  DPO rewriting on skill graphs, AlgebraicDynamics, AlgebraicPetri,
  AlgebraicRewriting, Decapodes, categorical algebra in Julia.
---

# Catlab.jl Interleave

Bridge connecting AlgebraicJulia/Catlab.jl (categorical algebra in Julia) to skill graphs.

## Catlab Core Concepts

### ACSets (Attributed C-Sets)

The universal data structure. A schema defines objects, homomorphisms, and attribute types. An ACSet instance is a functor from that schema category to Set.

```julia
>>>>>>> origin/main
@present SchGraph(FreeSchema) begin
  V::Ob; E::Ob
  src::Hom(E,V); tgt::Hom(E,V)
end

<<<<<<< HEAD
# Attributed: add attribute types
=======
>>>>>>> origin/main
@present SchWeightedGraph <: SchGraph begin
  T::AttrType
  weight::Attr(E,T)
end

const WeightedGraph = ACSetType(SchWeightedGraph, index=[:src,:tgt])
```

<<<<<<< HEAD
Every diagram, network, and model in the ecosystem is an ACSet.

### Wiring Diagrams as ACSets

SchAttributedWiringDiagram with Box/InPort/OutPort/Wire. Boxes = operations/processes, wires = data flow. Used to compose dynamical systems, Petri nets, and more.

### Decorated Cospans

Functor L: A -> X gives "open" ACSets. OpenGraph with hypergraph category structure. Operations: `compose`, `otimes` (monoidal product), `mcopy`, `mmerge`, `delete`, `create`. Enable compositional modeling of open systems.
=======
### Wiring Diagrams as ACSets

SchAttributedWiringDiagram with Box/InPort/OutPort/Wire. Boxes = operations, wires = data flow. Used to compose dynamical systems, Petri nets, and more.

### Decorated Cospans

Functor L: A -> X gives "open" ACSets. Operations: `compose`, `otimes` (monoidal product), `mcopy`, `mmerge`, `delete`, `create`. Enable compositional modeling of open systems.
>>>>>>> origin/main

### Downstream Ecosystem

```
AlgebraicJulia/Catlab.jl (foundation)
<<<<<<< HEAD
  |- AlgebraicDynamics.jl     <- dynamical systems via decorated cospans
  |- AlgebraicPetri.jl        <- Petri nets with reaction network semantics
  |- AlgebraicRewriting.jl    <- DPO/SPO graph rewriting on ACSets
  |- CategoricalTensorNetworks.jl <- tensor contractions as string diagrams
  |- CombinatorialSpaces.jl   <- simplicial sets, discrete exterior calculus
  |- DataMigrations.jl        <- functorial data migration between schemas
  |- DiagrammaticEquations.jl <- physics equations as decorated cospans
  |- Decapodes.jl             <- multiphysics simulation via DEC
```

**No probabilistic/inference capabilities** -- must come from downstream packages or bridges. This is where `monad-bayes-asi-interleave` fills the gap.

## GF(3) Tripartite Tag

`algebraic-dynamics(-1) otimes catlab-asi-interleave(0) otimes algebraic-rewriting(+1) = 0`

Dynamics (-1) x Foundation (0) x Rewriting (+1) = balanced categorical stack.

---

## ASI Integration Points

### 1. acsets / acsets-algebraic-databases / acsets-relational-thinking <-> ACSets Core

Model the ASI skill graph as an ACSet for relational querying:

```julia
@present SchASISkills(FreeSchema) begin
=======
  |- AlgebraicDynamics.jl     -- dynamical systems via decorated cospans
  |- AlgebraicPetri.jl        -- Petri nets with reaction network semantics
  |- AlgebraicRewriting.jl    -- DPO/SPO graph rewriting on ACSets
  |- CategoricalTensorNetworks.jl -- tensor contractions as string diagrams
  |- CombinatorialSpaces.jl   -- simplicial sets, discrete exterior calculus
  |- DataMigrations.jl        -- functorial data migration between schemas
  |- DiagrammaticEquations.jl -- physics equations as decorated cospans
  |- Decapodes.jl             -- multiphysics simulation via DEC
```

## Integration Points

### Skill Graph as ACSet

```julia
@present SchSkills(FreeSchema) begin
>>>>>>> origin/main
  Skill::Ob; Edge::Ob; Hub::Ob
  src::Hom(Edge,Skill); tgt::Hom(Edge,Skill)
  hub_ref::Hom(Hub,Skill)
  SkillName::AttrType; TritVal::AttrType; Category::AttrType
  name::Attr(Skill,SkillName)
<<<<<<< HEAD
  trit::Attr(Skill,TritVal)        # -1, 0, +1
  category::Attr(Skill,Category)   # development | meta | ai-agents | ...
end

const ASISkills = ACSetType(SchASISkills, index=[:src,:tgt,:hub_ref])
skills = ASISkills()

# Conjunctive query: all GF(3)-balanced triads
gf3_triads(s) = filter(parts(s,:Edge)) do e
  t_src = s[s[e,:src], :trit]
  t_tgt = s[s[e,:tgt], :trit]
  (t_src + t_tgt) % 3 == 0
end
```

### 2. algebraic-rewriting / topos-adhesive-rewriting <-> DPO/SPO Rewriting

Double-pushout rewriting for safe skill graph mutation (MONOTONIC_SKILL_INVARIANT):
=======
  trit::Attr(Skill,TritVal)
  category::Attr(Skill,Category)
end

const Skills = ACSetType(SchSkills, index=[:src,:tgt,:hub_ref])
```

### DPO Rewriting for Safe Skill Graph Mutation
>>>>>>> origin/main

```julia
using AlgebraicRewriting

# DPO rule: add bridge skill to hub (never delete)
<<<<<<< HEAD
# L -> K <- R where |R| >= |L| always
add_bridge_rule = Rule(
  ACSetTransformation(L, K),   # L: match hub pattern
  ACSetTransformation(R, K),   # R: hub + new bridge skill
=======
# L -> K <- R where |R| >= |L| always (monotonic)
add_bridge_rule = Rule(
  ACSetTransformation(L, K),
  ACSetTransformation(R, K),
>>>>>>> origin/main
)
new_skills = rewrite(add_bridge_rule, current_skills)
@assert nparts(new_skills, :Skill) >= nparts(current_skills, :Skill)
```

<<<<<<< HEAD
SPO rewriting available for partial matches (non-adhesive contexts).

### 3. discopy / discopy-operads <-> Wiring Diagram Composition

Catlab's wiring diagrams and DisCoPy's string diagrams are the same mathematical object:

```julia
# ASI skill composition as wiring diagram
=======
### Wiring Diagram Composition

```julia
# Skill composition as wiring diagram
>>>>>>> origin/main
wd = @program SchSkillOp (validator::Val, coordinator::Coord, generator::Gen) begin
  validated = validator(input)
  coordinated = coordinator(validated)
  result = generator(coordinated)
  return result
end
<<<<<<< HEAD
# This WiringDiagram ACSet can be exported to DisCoPy format
```

Bridge: Julia WiringDiagram ACSet <-> Python DisCoPy Diagram via JSON serialization.

### 4. topos-catcolab / catcolab-* <-> CatColab Collaborative Modeling

CatColab is the web frontend to Catlab. Skills: `catcolab-ologs`, `catcolab-petri-nets`, `catcolab-stock-flow`, `catcolab-causal-loop`, `catcolab-decapodes`. All CatColab models are ACSets underneath.

### 5. interaction-nets <-> Decorated Cospans / Hypergraph Categories

Decorated cospans give OpenGraph a hypergraph category structure. Operations: `compose` (sequential), `otimes` (parallel), `mcopy` (fan-out), `mmerge` (fan-in), `delete`, `create`. Interaction nets are the computational model; decorated cospans are the categorical semantics.

### 6. crn-topology <-> AlgebraicPetri Reaction Networks
=======
# WiringDiagram ACSet can be exported to DisCoPy format via JSON
```

### AlgebraicPetri Reaction Networks
>>>>>>> origin/main

```julia
using AlgebraicPetri

<<<<<<< HEAD
# Chemical reaction network as Petri net ACSet
=======
>>>>>>> origin/main
sir_model = LabelledPetriNet([:S,:I,:R],
  :infection => ((:S,:I) => (:I,:I)),
  :recovery  => (:I => :R)
)
<<<<<<< HEAD
# Compose via decorated cospans
open_sir = Open(sir_model, [:S], [:R])
```

Connects to `crn-topology` for topological analysis of reaction networks.

### 7. dynamical-system-functor / coupled-system <-> AlgebraicDynamics
=======
open_sir = Open(sir_model, [:S], [:R])
```

### AlgebraicDynamics
>>>>>>> origin/main

```julia
using AlgebraicDynamics, Catlab

<<<<<<< HEAD
# Open continuous dynamical system
=======
>>>>>>> origin/main
rb_system = ContinuousResourceSharer{Float64}(
  [:temperature, :velocity, :pressure],
  (u, p, t) -> rb_dynamics(u, p, t)
)
<<<<<<< HEAD
# Compose via wiring diagram
=======
>>>>>>> origin/main
full_system = oapply(boundary_diagram, [rb_system, thermal_bc])
solution = solve(ODEProblem(full_system, u0, tspan), Tsit5())
```

<<<<<<< HEAD
### 8. julia-scientific <-> Julia Runtime for Catlab

Catlab requires Julia >= 1.10. Entry points: `julia-scientific`, `julia-gay`. Enzyme.jl autodiff works with AlgebraicDynamics ODE solvers.

### 9. topos-unified / topos-generate <-> Topos-Theoretic Foundations

Catlab implements presentable categories, limits/colimits, Kan extensions. The topos-theoretic skills (`topos-unified`, `topos-generate`, `effective-topos`) provide the foundation that Catlab operationalizes in code.

### 10. monad-bayes-asi-interleave <-> Fills Probabilistic Gap

Catlab has **no built-in probabilistic inference**. `monad-bayes-asi-interleave` provides SMC/MCMC/PMMH/RMSMC stacks. The bridge: Catlab composes the model structure, monad-bayes performs inference on it.

### 11. vertex-ai-protein-interleave <-> Protein Reaction Networks

AlgebraicPetri reaction networks model biochemical pathways. Protein folding/docking pipelines from `vertex-ai-protein-interleave` can use Catlab ACSets to represent reaction networks, pathway composition, and multi-target drug interaction graphs.

---

## ASI Skill Graph as an ACSet (Self-Modeling)

The ASI skill graph itself is naturally an ACSet:

```julia
# Skills = objects, edges = morphisms, GF(3) trits = attributes
@present SchASIGraph(FreeSchema) begin
  Skill::Ob
  Edge::Ob
  src::Hom(Edge,Skill)
  tgt::Hom(Edge,Skill)
  # Attribute types
  Name::AttrType; Trit::AttrType; Role::AttrType; Version::AttrType
  # Attributes
  name::Attr(Skill,Name)
  trit::Attr(Skill,Trit)          # GF(3): -1, 0, +1
  role::Attr(Skill,Role)          # BRIDGE | HUB | LEAF | ERGODIC
  version::Attr(Skill,Version)
  edge_type::Attr(Edge,Name)      # :citation | :behavioral | :trit_equiv
end

# Invariants as ACSet constraints:
# 1. MONOTONIC: nparts(g, :Skill) >= 1360 (never decreases)
# 2. GF3_CONSERVATION: for any triad (s1,s2,s3), sum of trits = 0 mod 3
# 3. HUB_REACHABILITY: 17 hub skills; every leaf reachable from >= 1 hub
```

This enables: conjunctive queries over the skill graph, functorial data migration between schema versions, DPO rewriting for safe skill addition, and wiring diagram visualization of skill pipelines.

---

## Connection to ASI Topos Stories

| Story (task) | Catlab Connection |
|-------------|-------------------|
| Task 21: Categorical worlding kit | Catlab.jl engine + CatColab UI + UnwiringDiagrams.jl |
| Task 22: Compositional game theory | Wiring diagrams encode open game composition |
| Task 23: Nonlinear dynamics observatory | AlgebraicDynamics for attractor ODE composition |
| Task 24: ASI skill federation | ACSet as skill registry; DPO rewriting for safe addition |
| Task 20: Self-walking proof pipeline | AlgebraicRewriting as proof rewrite system |

---

## Gap Registry

| Capability | Status | Filled By |
|-----------|--------|-----------|
| Probabilistic inference on ACSets | MISSING in Catlab | `monad-bayes-asi-interleave` |
| GPU-accelerated ACSet operations | MISSING | Future: CUDA.jl + ACSet kernels |
| ACSet <-> DuckDB serialization | PARTIAL | `duckdb-ies` (Parquet round-trip) |
| ACSet <-> JSON-RPC for MCP | MISSING | Need: syrup/JSON bridge for ACSets |
| Real-time collaborative ACSets | PARTIAL | CatColab (web only, no MCP) |
| ACSet diff/merge (CRDT semantics) | MISSING | `crdt` skill + DPO rewriting |
| Tensor network contraction at scale | MISSING | CategoricalTensorNetworks exists but no GPU |
| Discrete exterior calculus on DGX | MISSING | Decapodes + CUDA offload needed |

---

## Related ASI Skills

- `acsets` / `acsets-relational-thinking` / `acsets-algebraic-databases` -- core ACSet skills
- `algebraic-rewriting` / `topos-adhesive-rewriting` -- DPO/SPO rewriting on ACSets
- `discopy` / `discopy-operads` -- Python string diagram companion to Catlab
- `catcolab-ologs` / `catcolab-petri-nets` / `catcolab-stock-flow` / `catcolab-decapodes` -- CatColab frontends
- `interaction-nets` -- computational model for decorated cospan composition
- `crn-topology` -- topological analysis of AlgebraicPetri reaction networks
- `dynamical-system-functor` / `coupled-system` -- AlgebraicDynamics integration
- `julia-scientific` / `julia-gay` -- Julia ecosystem entry points
- `topos-unified` / `topos-generate` / `effective-topos` -- topos-theoretic foundations
- `monad-bayes-asi-interleave` -- fills probabilistic inference gap
- `vertex-ai-protein-interleave` -- protein reaction networks via AlgebraicPetri
- `structured-decomp` -- structured decompositions = open graphs (Catlab cospans)
- `enzyme-autodiff` -- Enzyme.jl autodiff for AlgebraicDynamics simulation
- `wolframite-compass` -- Wolfram -> Catlab via Julia bridge
- `string-diagram-rewriting-protocol` -- rewriting protocol for wiring diagrams
=======
### Runtime

Catlab requires Julia >= 1.10. Enzyme.jl autodiff works with AlgebraicDynamics ODE solvers.

## Gap Registry

| Capability | Status | Notes |
|-----------|--------|-------|
| Probabilistic inference on ACSets | MISSING in Catlab | Use monad-bayes bridge |
| GPU-accelerated ACSet operations | MISSING | Future: CUDA.jl + ACSet kernels |
| ACSet <-> DuckDB serialization | PARTIAL | Parquet round-trip |
| ACSet <-> JSON-RPC for MCP | MISSING | Need syrup/JSON bridge |
| ACSet diff/merge (CRDT semantics) | MISSING | DPO rewriting approach |
>>>>>>> origin/main
