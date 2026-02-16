# ACSets / Catlab bridge (minimal)

StructuredDecompositions.jl is built on Catlab and ACSet concepts. Use this
as a quick reminder for the types that show up in examples.

## Core types used here
- `Graph` and `SymmetricGraph` from `Catlab.Graphs` (ACSets under the hood).
- `ACSetTransformation` for structure-preserving maps between graphs.
- `FinSet`, `FinFunction`, and `FinDomFunctor` from `Catlab.CategoricalAlgebra`.

## Minimal setup
```julia
using Catlab
using Catlab.CategoricalAlgebra
using Catlab.Graphs
```

## ACSet schema sketch (optional)
If you need to define a custom schema or graph-like ACSet, consult the
`acsets-algebraic-databases` skill for full patterns. The minimal graph schema
looks like:

```julia
@present SchGraph(FreeSchema) begin
  V::Ob
  E::Ob
  src::Hom(E, V)
  tgt::Hom(E, V)
end

@acset_type Graph(SchGraph, index=[:src, :tgt])
```

## Transformations
```julia
# ACSetTransformation(domain, codomain; V, E) maps parts by index arrays.
f = ACSetTransformation(dom_graph, cod_graph; V=[...], E=[...])
```
