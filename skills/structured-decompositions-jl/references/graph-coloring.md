# Graph coloring example (ASCII variant)

This is a compact, ASCII-only adaptation of the graph-coloring example from
`/Users/bob/ies/StructuredDecompositions.jl/docs/src/pages/DecidingSheaves.md`.
It illustrates how to build a structured decomposition manually and apply the
sheaf decision procedure.

```julia
using StructuredDecompositions
using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphs

# Define a coloring sheaf (contravariant).
struct Coloring
  n
  func
end

K(n) = complete_graph(Graph, n)
Coloring(n) = Coloring(n, g -> homomorphisms(g, K(n)))

(c::Coloring)(X::Graph) = FinSet(c.func(X))
function (c::Coloring)(f::ACSetTransformation)
  G1, G2 = dom(f), codom(f)
  cG1, cG2 = c(G1), c(G2)
  FinFunction(lambda2 -> compose(f, lambda2), cG2, cG1)
end

skeletalColoring(n) = skeleton ∘ Coloring(n)

# Build a decomposition of a 7-cycle using two bags and an adhesion.
H1 = @acset Graph begin
  V = 3
  E = 2
  src = [1, 2]
  tgt = [2, 3]
end

H12 = @acset Graph begin
  V = 2
end

H2 = @acset Graph begin
  V = 4
  E = 3
  src = [1, 2, 3]
  tgt = [2, 3, 4]
end

Gs = @acset Graph begin
  V = 2
  E = 1
  src = [1]
  tgt = [2]
end

# Transformations for the diagram.
Gamma0 = Dict(1 => H1, 2 => H2, 3 => H12)
Gamma = FinDomFunctor(
  Gamma0,
  Dict(
    1 => ACSetTransformation(Gamma0[3], Gamma0[1], V=[1, 3]),
    2 => ACSetTransformation(Gamma0[3], Gamma0[2], V=[4, 1]),
  ),
  ∫(Gs)
)

my_decomp = StrDecomp(Gs, Gamma)

# Decide colorability with a sheaf.
colorability_test(n, test_case) =
  is_homomorphic(ob(colimit(test_case)), K(n)) ==
  decide_sheaf_tree_shape(skeletalColoring(n), test_case)[1]
```

Notes:
- This example assumes the Catlab stack is available and loaded.
- `decide_sheaf_tree_shape` returns `(ok::Bool, witness_decomp)`.
- The original doc uses Unicode identifiers; this version is ASCII-only.
