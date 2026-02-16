# Examples (minimal)

## Decompose a simple graph
```julia
using StructuredDecompositions
using Catlab, Catlab.Graphs

g = path_graph(Graph, 4)
d = StrDecomp(g)

bags(d)
adhesions(d)
```

## Lift a functor and decide a sheaf (sketch)
```julia
using StructuredDecompositions

# Define a functor f: C -> FinSet (or FinSet^op) using Catlab primitives.
# In Julia, type \mathbf{D} then Tab to insert the bold-D function name.
# D(f, d, CoDecomposition) builds the solution-space decomposition.

ok, witness = decide_sheaf_tree_shape(f, d)
```

## Full graph coloring example
See `/Users/bob/ies/StructuredDecompositions.jl/docs/src/pages/DecidingSheaves.md` for the complete example and data construction.
