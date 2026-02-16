---
name: structured-decompositions-jl
description: Use when users ask about StructuredDecompositions.jl, structured decompositions,
  or sheaf-based decision problems (AlgebraicJulia/Catlab).
---

# StructuredDecompositions.jl

You help with Julia tasks involving StructuredDecompositions.jl. Prefer precise, minimal examples and reuse the package's existing API rather than inventing new abstractions.

## Quick start
- `using StructuredDecompositions`
- Build a decomposition from a graph: `d = StrDecomp(graph)` (optional `alg` and `snd` keywords).
- Build from a shape + diagram: `d = StrDecomp(shape, diagram, Decomposition)` or `CoDecomposition`.
- Inspect: `bags(d)`, `adhesions(d)`, `adhesionSpans(d)` (pass `true` for indexed pairs).
- Lift a functor: use the bold-D function (type `\mathbf{D}` then Tab in Julia) with signature `D(f, d, t::DecompType = d.decomp_type)`.
- Decide a sheaf-encoded problem: `ok, witness = decide_sheaf_tree_shape(f, d)`.

## Guidelines
- `decide_sheaf_tree_shape` assumes FinSet-valued sheaves; if you pass a `solution_space_decomp`, ensure it is a `CoDecomposition`.
- `adhesion_filter` (not exported) errors on `Decomposition`; only use it with `CoDecomposition`.
- Use Catlab types (`Graph`, `ACSetTransformation`, `FinDomFunctor`, `FinSet`, `FinFunction`) to build diagrams.
- Prefer small, runnable snippets. If a full example is large, summarize and point to the references.
- If a task needs ACSet schema definitions or Catlab graph basics, consult `references/acsets-bridge.md` or load the `acsets-algebraic-databases` skill.

## References
- `references/overview.md` for the API map and key behaviors.
- `references/examples.md` for minimal usage sketches.
- `references/graph-coloring.md` for an ASCII-only end-to-end coloring example.
- `references/acsets-bridge.md` for ACSet/Catlab basics used by this package.

## Scripts
- `scripts/quickstart.jl` builds a simple decomposition and prints bags/adhesions.

## Example triggers
- "Make a structured decomposition for this graph."
- "Lift a functor over a decomposition and decide a sheaf."
- "How do I use decide_sheaf_tree_shape for graph coloring?"