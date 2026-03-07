---
name: relegant
description: Cross-domain theory connecting Sprague-Grundy computation, graph coloring, Möbius inversion, string diagram composition, and nimber arithmetic through incidence algebras
---

# Relegant

**Relegant** (neologism): structures that are *relevant* through *relegation* — demoted from one domain, they re-emerge as foundational in another.

## Cross-Domain Thesis

Five structures share a single algebraic spine: the **incidence algebra of a locally finite category**. The mex operation, Möbius inversion, deletion-contraction, nim-sum, and string diagram composition are all operations in or derived from incidence algebras.

```
                    Incidence Algebra
                    /       |       \
                   /        |        \
    Möbius Inversion    mex (SG)    Deletion-Contraction
         |                |               |
   Chromatic Poly    Grundy Values    Tutte Poly
         |                |               |
    Bond Lattice     Game DAG        Graph Structure
         \               |              /
          \              |             /
           String Diagram Composition
                    |
              Nimber Arithmetic
                 (On_2 / GF(2^n))
```

## When to Use

- Bridging between the "two Grundy numbers" (game-theoretic SG value vs. greedy-coloring Grundy chromatic number)
- Composing games using string diagram calculus (sequential + parallel)
- Reasoning about nimber-preserving reductions between game rulesets
- Computing chromatic polynomials via Möbius inversion on bond lattices

## The Relegant Invariant

For any relegant analysis, verify:

1. **Incidence algebra coherence**: The poset/DAG/lattice structure admits a well-defined incidence algebra with invertible zeta function.
2. **Functorial solution**: Game values are computed by a functor from the game category to the nimber field (On_2).
3. **Conservation**: Under diagrammatic composition, nimber values are preserved (nimber-preserving reduction).
4. **Möbius-mex duality**: Möbius inversion on the structure lattice and mex computation on the game DAG yield compatible results.

## Computational Module Signatures

### grundy_compute(game_dag)
Retrograde analysis on a DAG. Topological sort, then mex bottom-up. Returns mapping from positions to Grundy values.

### nimber_ops(a, b, op)
Nim-sum (XOR) and nim-product (Lenstra's algorithm for Fermat 2-power decomposition). Operates over On_2.

### chromatic_mobius(graph)
Chromatic polynomial via bond lattice enumeration + Möbius inversion. Returns `P(G, k)` as a callable.

### game_compose(games, wiring)
String diagram composition via hypergraph wiring. Sequential = categorical composition; parallel = monoidal product (nim-sum of values); feedback = traced monoidal structure.

## Key Post-Training References

### Categorical / Diagrammatic Game Theory
- Piedeleu, "The Algebra of Parity Games" (arXiv:2501.18499, 2025) — sound and complete string diagram axiomatization for parity games
- Watanabe et al., "Compositional Solution of Mean Payoff Games by String Diagrams" (arXiv:2307.08034, 2024) — order-of-magnitude speedups via functorial solution, implemented in Haskell
- Watanabe, "Pareto Fronts for Compositionally Solving String Diagrams of Parity Games" (arXiv:2406.17240, 2024)
- Basic et al., "Categories of impartial rulegraphs and gamegraphs" (arXiv:2312.00650, IJGT 2024)

### Nimber Complexity
- Burke, Ferland, Teng, "Nimber-Preserving Reductions and Homomorphic Sprague-Grundy Game Encodings" (arXiv:2109.05622, TCS 2024) — Generalized Geography is SG-complete; graph coloring rulesets live in this complexity class

### String Diagram Rewriting
- "Graphical Rewriting for Diagrammatic Reasoning in Monoidal Categories in Lean4" (ITP 2024)
