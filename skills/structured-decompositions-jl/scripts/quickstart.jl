# Quickstart: build a decomposition and inspect its parts.

using StructuredDecompositions
using Catlab, Catlab.Graphs

# Simple path graph with 4 vertices.
g = path_graph(Graph, 4)

# Clique-tree decomposition of the graph.
d = StrDecomp(g)

println("bags:")
for (i, bag) in enumerate(bags(d))
  println("  bag ", i, ": ", bag)
end

println("adhesions:")
for (i, adh) in enumerate(adhesions(d))
  println("  adhesion ", i, ": ", adh)
end
