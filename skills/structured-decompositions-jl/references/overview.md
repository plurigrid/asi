# StructuredDecompositions.jl overview

This skill targets the local repo at `/Users/bob/ies/StructuredDecompositions.jl`.

## Modules and exports
- `StructuredDecompositions` reexports:
  - `Decompositions` (core types and constructors)
  - `FunctorUtils` (small helper functors)
  - `DecidingSheaves` (decision procedure)

## Core types and constructors
- `StructuredDecomposition{G,C,D}`: abstract diagram type.
- `StrDecomp{G,C,D}`: concrete decomposition with fields `decomp_shape`, `diagram`, `decomp_type`, `domain`.
- `DecompType`: `Decomposition` or `CoDecomposition`.

Constructors:
- `StrDecomp(shape, diagram)`: defaults to `Decomposition`.
- `StrDecomp(shape, diagram, decomp_type)`: validates adhesion spans before returning.
- `StrDecomp(graph::HasGraph; alg=..., snd=...)`: builds a clique-tree-based decomposition of a simple graph.

## Inspection helpers
- `bags(d)` / `bags(d, true)`
- `adhesions(d)` / `adhesions(d, true)`
- `adhesionSpans(d)` / `adhesionSpans(d, true)`

## Operations
- `colimit(d)` and `limit(d)` compute the colimit/limit of the underlying diagram.
- Bold-D functor lift: type `\mathbf{D}` then Tab in Julia. Signature:
  - `D(f, d, t::DecompType = d.decomp_type)`
  - Lifts a functor `f` over a structured decomposition `d`.

## FunctorUtils
- `vs(::Graph)` and `vs(::ACSetTransformation)`
- `skeleton(::FinSet)` and `skeleton(::FinFunction)`

## DecidingSheaves
- `decide_sheaf_tree_shape(f, d, solution_space_decomp = D(f, d, CoDecomposition)) -> (Bool, witness)`
- `adhesion_filter(i, d)` is internal (not exported) and expects `CoDecomposition`.

## Notes and gotchas
- `decide_sheaf_tree_shape` assumes FinSet-valued sheaves and repeatedly filters adhesion spans.
- `adhesion_filter` raises an error if called on a `Decomposition`.
