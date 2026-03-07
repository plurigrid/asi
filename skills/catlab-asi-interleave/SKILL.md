---
name: catlab-asi-interleave
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
@present SchGraph(FreeSchema) begin
  V::Ob; E::Ob
  src::Hom(E,V); tgt::Hom(E,V)
end

@present SchWeightedGraph <: SchGraph begin
  T::AttrType
  weight::Attr(E,T)
end

const WeightedGraph = ACSetType(SchWeightedGraph, index=[:src,:tgt])
```

### Wiring Diagrams as ACSets

SchAttributedWiringDiagram with Box/InPort/OutPort/Wire. Boxes = operations, wires = data flow. Used to compose dynamical systems, Petri nets, and more.

### Decorated Cospans

Functor L: A -> X gives "open" ACSets. Operations: `compose`, `otimes` (monoidal product), `mcopy`, `mmerge`, `delete`, `create`. Enable compositional modeling of open systems.

### Downstream Ecosystem

```
AlgebraicJulia/Catlab.jl (foundation)
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
  Skill::Ob; Edge::Ob; Hub::Ob
  src::Hom(Edge,Skill); tgt::Hom(Edge,Skill)
  hub_ref::Hom(Hub,Skill)
  SkillName::AttrType; TritVal::AttrType; Category::AttrType
  name::Attr(Skill,SkillName)
  trit::Attr(Skill,TritVal)
  category::Attr(Skill,Category)
end

const Skills = ACSetType(SchSkills, index=[:src,:tgt,:hub_ref])
```

### DPO Rewriting for Safe Skill Graph Mutation

```julia
using AlgebraicRewriting

# DPO rule: add bridge skill to hub (never delete)
# L -> K <- R where |R| >= |L| always (monotonic)
add_bridge_rule = Rule(
  ACSetTransformation(L, K),
  ACSetTransformation(R, K),
)
new_skills = rewrite(add_bridge_rule, current_skills)
@assert nparts(new_skills, :Skill) >= nparts(current_skills, :Skill)
```

### Wiring Diagram Composition

```julia
# Skill composition as wiring diagram
wd = @program SchSkillOp (validator::Val, coordinator::Coord, generator::Gen) begin
  validated = validator(input)
  coordinated = coordinator(validated)
  result = generator(coordinated)
  return result
end
# WiringDiagram ACSet can be exported to DisCoPy format via JSON
```

### AlgebraicPetri Reaction Networks

```julia
using AlgebraicPetri

sir_model = LabelledPetriNet([:S,:I,:R],
  :infection => ((:S,:I) => (:I,:I)),
  :recovery  => (:I => :R)
)
open_sir = Open(sir_model, [:S], [:R])
```

### AlgebraicDynamics

```julia
using AlgebraicDynamics, Catlab

rb_system = ContinuousResourceSharer{Float64}(
  [:temperature, :velocity, :pressure],
  (u, p, t) -> rb_dynamics(u, p, t)
)
full_system = oapply(boundary_diagram, [rb_system, thermal_bc])
solution = solve(ODEProblem(full_system, u0, tspan), Tsit5())
```

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
