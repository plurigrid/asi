---
name: structured-decomp
description: StructuredDecompositions.jl sheaves on tree decompositions for FPT algorithms with bidirectional navigation
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Structured Decompositions Skill

> Sheaves on tree decompositions with bidirectional navigation

**Version**: 1.1.0
**Trit**: 0 (Ergodic - coordinates decomposition)

## bmorphism Contributions

> *"Compositional Algorithms on Compositional Data: Deciding Sheaves on Presheaves"*
> — [ACT 2023](https://act2023.github.io/papers/paper45.pdf), Benjamin Merlin Bumpus et al.

> *"any computational problem which can be represented as a sheaf with respect to these topologies can be decided in linear time on classes of inputs which admit decompositions of bounded width"*
> — [arXiv:2302.05575](https://arxiv.org/abs/2302.05575)

**Key Insight**: Structured decompositions define **Grothendieck topologies** on categories of data (adhesive categories). This leads to algorithms on objects of any C-set category - structures such as: symmetric graphs, directed graphs, hypergraphs, databases, simplicial complexes, port graphs.

**Implementation**: Concrete implementations in the [AlgebraicJulia](https://algebraicjulia.github.io/StructuredDecompositions.jl) ecosystem.

Related to bmorphism's work on:
- [plurigrid/act](https://github.com/plurigrid/act) - cognitive category theory building blocks
- [Towards Foundations of Categorical Cybernetics](https://arxiv.org/abs/2105.06332) - cybernetic systems via parametrised optics

## Core Concept

**StrDecomp** = Functor `d: ∫G → C` where:
- **∫G** = category of elements of shape graph
- **C** = target category (Graph, FinSet, etc.)

```julia
using StructuredDecompositions

# Create decomposition from graph
d = StrDecomp(graph)

# Access components
bags(d)           # Local substructures
adhesions(d)      # Overlaps (shared boundaries)
adhesionSpans(d)  # Span morphisms
```

## The 𝐃 Functor

Lifts decision problems to decomposition space:

```julia
# Define problem as functor
k_coloring(G) = homomorphisms(G, K_k)

# Lift and solve
solution = 𝐃(k_coloring, decomp, CoDecomposition)
(answer, witness) = decide_sheaf_tree_shape(k_coloring, d