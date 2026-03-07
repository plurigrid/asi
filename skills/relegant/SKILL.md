---
name: relegant
description: >
  Relegant theory: the bridge between Sprague-Grundy nimber computation, graph coloring
  (chromatic polynomial, Grundy chromatic number), Mobius inversion on posets, diagrammatic
  rewriting via string diagrams, and nimber arithmetic over On_2. Use when analyzing
  combinatorial games on graphs, composing games diagrammatically, computing Grundy values
  or chromatic polynomials via Mobius inversion, or reasoning about nimber field operations.
version: 0.1.0
license: Apache-2.0
metadata:
  trit: 0
  trit_label: ERGODIC
  author: bmorphism
  domain: combinatorial-game-theory
  keywords: sprague-grundy nimber graph-coloring mobius-inversion diagrammatic-rewriting
---

# Relegant

**Relegant** (adj., neologism): of or pertaining to structures that are *relevant* through
*relegation* — demoted from one domain, they re-emerge as foundational in another. The Grundy
value is "relegated" from graph coloring to game theory; the Mobius function is "relegated"
from number theory to poset combinatorics; string diagrams are "relegated" from physics to
game solving. Relegant theory studies these cross-domain inversions.

## Core Thesis

Five structures share a single algebraic spine: the **incidence algebra of a locally finite
category**. The mex operation, Mobius inversion, deletion-contraction, nim-sum, and string
diagram composition are all operations in or derived from incidence algebras. GF(2) arithmetic
pervades the value side (nimbers), while Mobius inversion organizes the structure side (posets,
lattices, game DAGs).

```
                    Incidence Algebra
                    /       |       \
                   /        |        \
    Mobius Inversion    mex (SG)    Deletion-Contraction
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

## When to Use This Skill

- Computing Sprague-Grundy values for impartial games, especially graph games
- Analyzing graph coloring as a game (game chromatic number, Grundy chromatic number)
- Computing chromatic polynomials via Mobius inversion on bond lattices
- Composing games using string diagram calculus (sequential + parallel)
- Solving composed games by equational rewriting on diagrams
- Nimber arithmetic (nim-sum, nim-product, Conway field On_2)
- Bridging between the "two Grundy numbers" (game-theoretic vs. greedy-coloring)
- Reasoning about nimber-preserving reductions between game rulesets

## Five Pillars

### 1. Sprague-Grundy (Nimber Computation)

Every impartial game under normal play is equivalent to a Nim heap. The Grundy value:

```
G(p) = mex({G(q) : q is an option of p})
```

Disjunctive sum of games: `G(A + B) = G(A) XOR G(B)` (nim-sum).

**Nimber-preserving reductions** (Burke-Ferland-Teng 2024): A ruleset R is
*Sprague-Grundy complete* if every polynomially-short impartial game reduces to R
under poly-time nimber-preserving reductions. Generalized Geography is SG-complete.
Graph coloring rulesets (Proper-K-Coloring, oriented coloring, 2-distance coloring)
live in this complexity class.

### 2. Graph Coloring (Chromatic Polynomial + Grundy Chromatic Number)

Two distinct "Grundy" concepts collide here:

| Concept | Definition | Domain |
|---------|-----------|--------|
| Sprague-Grundy value G(p) | mex of option values | Combinatorial game theory |
| Grundy chromatic number Gamma(G) | max colors under worst-case greedy | Graph theory |

The **game chromatic number** chi_g(G): Alice and Bob alternately color vertices; Alice
minimizes, Bob maximizes colors used. This *is* an impartial game analyzable via
Sprague-Grundy when both players have identical move sets.

The **chromatic polynomial** P(G, k) counts proper k-colorings. Computed via:
- Deletion-contraction: `P(G, k) = P(G\e, k) - P(G/e, k)`
- Mobius inversion on the bond lattice (Pillar 3)
- Specialization of Tutte polynomial: `P(G, k) = (-1)^{|V|-c} k^c T(G; 1-k, 0)`

### 3. Mobius Inversion (Rota's Framework)

The Mobius function on a locally finite poset P:

```
mu(s, s) = 1
mu(s, u) = -sum_{s <= t < u} mu(s, t)    for s < u
```

**Structural parallel with mex**: Both compute a value at a node by examining all
predecessors and applying an exclusion/inversion operation. Both are instances of
computing inverses in incidence algebras.

The chromatic polynomial via bond lattice L_G:
```
P(G, k) = sum_{pi in L_G} mu(0_hat, pi) * k^{|pi|}
```
where |pi| is the number of blocks in partition pi.

**Key insight**: The Mobius function mu is the *inverse of the zeta function* in the
incidence algebra. The Sprague-Grundy function can be viewed as computing a *section*
of the zeta function of the game DAG, with mex as a characteristic-0 analogue of
Mobius inversion mapping into ordinals rather than integers.

### 4. Diagrammatic Rewriting (String Diagram Calculus)

Games are morphisms of a symmetric monoidal category. This gives:

- **Sequential composition** = categorical composition (play game A, then game B)
- **Parallel play** = monoidal product (play A and B simultaneously)
- **Solution** = a functor from game category to value category

Key results enabling this:

- **Joyal's category of Conway games** (1977): compact closed, *-autonomous.
  Morphisms = winning strategies for Left playing second in H - G.
- **Piedeleu (2025)**: Parity games get a *sound and complete* axiomatization as
  string diagrams. Games are solved by equational reasoning on diagrams.
- **Watanabe et al. (2024)**: Mean payoff games composed as string diagrams;
  solution is a functor. Implemented in Haskell; order-of-magnitude speedups.
- **Cockett-Cruttwell-Saff**: Category of finite games is *initial* among
  combinatorial-game categories (universal property for game invariants).

**Rewriting theory**: Bonchi et al.'s DPO (double-pushout) rewriting of hypergraphs
gives sound and complete rewriting for string diagrams with Frobenius or symmetric
monoidal structure.

### 5. Nimber Arithmetic (On_2 = Algebraic Closure of GF(2))

Conway proved that ordinals with nim-addition (XOR) and nim-multiplication form an
algebraically closed field of characteristic 2. For each n, nimbers below 2^{2^n}
form GF(2^{2^n}).

Operations:
- **Nim-sum**: bitwise XOR. O(log n). Each nimber is its own additive inverse.
- **Nim-product**: recursive via Lenstra's algorithm. For Fermat 2-powers
  alpha = 2^{2^k}, nim-product with smaller nimbers = ordinary product.
  General case uses distributivity + the identity for Fermat 2-power products.

The finite nimbers form the algebraic closure of GF(2) = direct limit of GF(2^{2^n}).

## Computational Modules

When implementing relegant computations, use these patterns:

### grundy_compute(game_dag)
Retrograde analysis on a DAG. Topological sort, then compute mex bottom-up.
```python
def grundy(dag, pos, memo={}):
    if pos in memo: return memo[pos]
    reachable = {grundy(dag, q, memo) for q in dag[pos]}
    val = mex(reachable)
    memo[pos] = val
    return val

def mex(s):
    i = 0
    while i in s: i += 1
    return i
```

### nimber_ops(a, b, op)
```python
def nim_sum(a, b):
    return a ^ b

def nim_product(a, b):
    if a < 2 or b < 2: return a * b
    # Find highest Fermat 2-power component
    k = highest_fermat_2power_exp(a)
    D = 1 << (1 << k)  # D = 2^{2^k}
    if a == D:
        if b < D: return a * b
        if b == D: return nim_product(3, D >> 1)  # D*D = (3/2)*D
    # Split and distribute
    ah, al = a >> k, a & ((1 << k) - 1)
    return nim_sum(nim_product(ah, b) << k, nim_product(al, b))
```

### chromatic_mobius(graph)
Compute chromatic polynomial via bond lattice + Mobius inversion.
```python
def chromatic_poly(G):
    partitions = bond_lattice(G)  # all partitions induced by edge subsets
    mu = mobius_function(partitions)
    # P(G, k) = sum over pi: mu(0_hat, pi) * k^|pi|
    return lambda k: sum(mu[pi] * k**num_blocks(pi) for pi in partitions)
```

### game_compose(games, wiring)
String diagram composition. The wiring diagram is a hypergraph specifying how
outputs of one game connect to inputs of another.
```
Sequential:  A ; B  = categorical composition
Parallel:    A | B  = monoidal product (nim-sum of values)
Feedback:    trace  = traced monoidal structure
```

## The Relegant Invariant

For any relegant analysis, verify:

1. **Incidence algebra coherence**: The poset/DAG/lattice structure admits a
   well-defined incidence algebra with invertible zeta function.
2. **Functorial solution**: Game values are computed by a functor from the game
   category to the nimber field (On_2).
3. **Conservation**: Under diagrammatic composition, nimber values are preserved
   (nimber-preserving reduction).
4. **Mobius-mex duality**: Mobius inversion on the structure lattice and mex
   computation on the game DAG yield compatible results.

## Key References

### Categorical / Diagrammatic Game Theory
- Piedeleu, "The Algebra of Parity Games" (arXiv:2501.18499, 2025)
- Watanabe et al., "Compositional Solution of Mean Payoff Games by String Diagrams" (arXiv:2307.08034, 2024)
- Watanabe, "Pareto Fronts for Compositionally Solving String Diagrams of Parity Games" (arXiv:2406.17240, 2024)
- Hedges et al., "Compositional Game Theory" (arXiv:1603.04641, LICS 2018)
- Cockett, Cruttwell, Saff, "Combinatorial Game Categories"
- Basic et al., "Categories of impartial rulegraphs and gamegraphs" (arXiv:2312.00650, IJGT 2024)

### Nimber Complexity
- Burke, Ferland, Teng, "Nimber-Preserving Reductions and Homomorphic Sprague-Grundy Game Encodings" (arXiv:2109.05622, TCS 2024)

### String Diagram Rewriting
- Bonchi et al., "String Diagram Rewrite Theory I" (JACM)
- Bonchi et al., "String Diagram Rewrite Theory II" (MSCS)
- "Graphical Rewriting for Diagrammatic Reasoning in Monoidal Categories in Lean4" (ITP 2024)

### Nimber Arithmetic / On_2
- Conway, On Numbers and Games (1976/2001)
- Lenstra, "On the algebraic closure of two" (1977)

### Mobius Inversion / Chromatic Polynomial
- Rota, "On the foundations of combinatorial theory I" (1964)
- Cioaba & Murty, "Mobius Inversion and Graph Colouring"

### Graph Coloring Games
- "Colouring games" in Topics in Chromatic Graph Theory (Cambridge)
- "Complexity of Grundy Coloring and Its Variants" (COCOA 2015)

## Examples

### Example 1: Nim on a Path Graph
Given P_4 (path on 4 vertices), compute the game Grundy value when players
alternately color vertices with first-fit:
- Grundy chromatic number Gamma(P_4) = 3 (greedy worst case)
- Game chromatic number chi_g(P_4) = 3 (adversarial play)
- Sprague-Grundy value of the coloring game depends on ruleset encoding

### Example 2: Chromatic Polynomial of K_4 via Mobius
Bond lattice of K_4 has 15 partitions. Mobius inversion yields:
P(K_4, k) = k(k-1)(k-2)(k-3)
Evaluating: P(K_4, 4) = 24 proper 4-colorings.

### Example 3: Composing Graph Games Diagrammatically
Two Nim-on-graph games G1, G2 composed in parallel:
```
┌───┐   ┌───┐
│ G1│ | │ G2│  =  G1 + G2  (disjunctive sum)
└───┘   └───┘
Grundy(G1 + G2) = Grundy(G1) XOR Grundy(G2)
```
Sequential composition (play G1, winner enters G2):
```
┌───┐ ; ┌───┐
│ G1│───│ G2│  =  G1 ; G2  (continuation game)
└───┘   └───┘
Requires full diagrammatic analysis (not just XOR)
```
