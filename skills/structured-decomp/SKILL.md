# structured-decomp - Sheaves on Tree Decompositions for FPT Algorithms

## Overview

StructuredDecompositions.jl implements **sheaf-theoretic decision procedures** on tree decompositions, enabling Fixed-Parameter Tractable (FPT) algorithms for NP-hard problems. This is the **Bumpus leg** of the Kleppmann-Bumpus-Gay Third path equivalence.

Key insight: Decision problems become **sheaf conditions** — local solutions glue to global solutions iff the sheaf condition is satisfied.

**Trit**: 0 (ERGODIC) - Coordinates categorical transport between local and global

## Core Formula

```
StrDecomp{G, C, D} <: Diagram{id, C, D}

d: ∫G → Span(C)     -- Decomposition (covariant, vortex +1)
d: ∫G → Cospan(C)   -- CoDecomposition (contravariant, antivortex -1)

Colorable(G, k) ⟺ ∃ sheaf section: decide_sheaf_tree_shape(Coloring(k), d) = true
Derangeable(G)  ⟺ ∃ fixed-point-free permutation over bags with gluing
```

## Predicates

| Predicate | Description | GF(3) Role |
|-----------|-------------|------------|
| `Colorable(G, k)` | k-coloring exists via sheaf decision | Obstruction (-1) |
| `Derangeable(d)` | Bags admit derangement with adhesion consistency | Transport (0) |
| `AdhesionConsistent(d)` | All adhesion spans agree at apex | Conservation |
| `TreeWidth(d, w)` | Max adhesion size ≤ w | Complexity bound |
| `SheafCondition(F, d)` | Local sections glue globally | Existence |
| `GF3Conserved(d)` | Σ trit over walk = 0 mod 3 | Balance |

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Structured Decompositions Pipeline                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│   Graph G              StrDecomp d              Sheaf Decision               │
│      │                     │                         │                       │
│      ▼                     ▼                         ▼                       │
│  ┌────────┐    ┌─────────────────────┐    ┌──────────────────────┐          │
│  │ Input  │───▶│  d: ∫G → Span(C)    │───▶│ decide_sheaf_tree    │          │
│  │ Graph  │    │  decomp_shape: G    │    │ _shape(F, d)         │          │
│  └────────┘    │  diagram: D         │    │                      │          │
│                │  decomp_type: Type  │    │ Returns: (bool, wit) │          │
│                └─────────────────────┘    └──────────────────────┘          │
│                         │                           │                        │
│                         ▼                           ▼                        │
│                ┌─────────────────┐         ┌──────────────────┐             │
│                │ bags(d)        │         │ Colorable?       │             │
│                │ adhesions(d)   │         │ Derangeable?     │             │
│                │ adhesionSpans  │         │ Hamiltonian?     │             │
│                └─────────────────┘         └──────────────────┘             │
│                                                                              │
│   DecompType                        Functorial Lift                          │
│      │                                   │                                   │
│      ▼                                   ▼                                   │
│  ┌─────────────────┐           ┌─────────────────────────┐                  │
│  │ Decomposition   │           │ 𝐃(F, d): 𝐃C → 𝐃E       │                  │
│  │   (+1 vortex)   │           │ Lifts F: C → E to      │                  │
│  │ CoDecomposition │           │ decomposition category  │                  │
│  │   (-1 antivortex)│          └─────────────────────────┘                  │
│  └─────────────────┘                                                         │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Triads (GF(3) = 0)

```
# Core Decomposition Bundle
dmd-spectral (-1) ⊗ structured-decomp (0) ⊗ koopman-generator (+1) = 0 ✓  [Decomposition]
sheaf-cohomology (-1) ⊗ structured-decomp (0) ⊗ colimit-reconstruct (+1) = 0 ✓  [Reconstruction]
three-match (-1) ⊗ structured-decomp (0) ⊗ gay-mcp (+1) = 0 ✓  [Core Walk]

# Kleppmann-Bumpus-Gay Path Equivalence
time-travel-crdt (-1) ⊗ structured-decomp (0) ⊗ gay-mcp (+1) = 0 ✓  [KBG Third]
persistent-homology (-1) ⊗ structured-decomp (0) ⊗ topos-generate (+1) = 0 ✓  [Topological]

# Chromatic Walk Integration
polyglot-spi (-1) ⊗ structured-decomp (0) ⊗ agent-o-rama (+1) = 0 ✓  [Multi-Agent]
shadow-goblin (-1) ⊗ structured-decomp (0) ⊗ gay-mcp (+1) = 0 ✓  [Trace Validation]
```

## Proof: Colorable as Random Walk

**Theorem (Colorability via Sheaf Walk)**: A graph G is k-colorable iff a random walk over the decomposition d with Coloring(k) sheaf terminates with non-empty global section.

```julia
# Coloring functor: Graph → FinSet^op
struct Coloring
  n::Int                              # number of colors
  func::Function                      # g -> homomorphisms(g, K(n))
end

K(n) = complete_graph(Graph, n)       # Complete graph on n vertices
Coloring(n) = Coloring(n, g -> homomorphisms(g, K(n)))

# Contravariant action on morphisms
(c::Coloring)(X::Graph) = FinSet(c.func(X))
(c::Coloring)(f::ACSetTransformation) = FinFunction(λ -> compose(f, λ), c(codom(f)), c(dom(f)))

# Decision procedure = random walk over tree decomposition
function decide_colorable(G::Graph, k::Int, d::StrDecomp)
  F = skeleton ∘ Coloring(k)
  (answer, witness) = decide_sheaf_tree_shape(F, d, 𝐃(F, d, CoDecomposition))
  return answer  # true iff k-colorable
end
```

**Random Walk Interpretation**:
1. Start at root bag b₀
2. Compute local colorings: `F(b₀) = Hom(b₀, K_k)`
3. Walk to adjacent bag b₁ via adhesion a₀₁
4. Filter: keep only colorings consistent on adhesion
5. Repeat until all bags visited
6. **Colorable** ⟺ non-empty set remains (global section exists)

**GF(3) Conservation**: Each bag visit has trit 0 (transport), adhesion filtering has trit -1 (constraint), coloring generation has trit +1 (creation). Walk conserves Σ trit = 0.

## Proof: Derangeable as Random Walk

**Theorem (Derangeability via Adhesion Consistency)**: A structured decomposition d is derangeable iff there exists a permutation π of bags such that π(b) ≠ b for all b, and adhesion spans are preserved.

```julia
# Derangement = fixed-point-free permutation preserving structure
function is_derangeable(d::StrDecomp)
  bs = bags(d)
  n = length(bs)
  
  # Generate candidate derangements (permutations with no fixed points)
  for π in permutations(1:n)
    if all(i -> π[i] ≠ i, 1:n)  # No fixed points
      if adhesion_preserving(d, π)
        return true
      end
    end
  end
  return false
end

# Check if permutation preserves adhesion structure
function adhesion_preserving(d::StrDecomp, π::Vector{Int})
  for (a, span) in adhesionSpans(d, true)
    (left_bag, right_bag) = endpoints(a)
    # Permuted adhesion must still connect valid bags
    if !valid_adhesion(d, π[left_bag], π[right_bag], span)
      return false
    end
  end
  return true
end
```

**Random Walk Interpretation**:
1. Start at arbitrary bag b₀
2. Propose swap: b₀ ↔ b₁ where b₁ ≠ b₀
3. Check adhesion consistency after swap
4. Walk to next bag, repeat
5. **Derangeable** ⟺ complete walk with no fixed points and all adhesions valid

**GF(3) Conservation**: Swap proposal (+1), consistency check (-1), transport to next bag (0). Each step sums to 0.

## API Reference

```julia
using StructuredDecompositions

# Construction
d = StrDecomp(graph, diagram)                    # Default: Decomposition
d = StrDecomp(graph, diagram, DecompType)        # Explicit type
d = StrDecomp(graph, diagram, CoDecomposition)   # Contravariant

# Accessors
bags(d)            # Vector of bag objects
adhesions(d)       # Vector of adhesion apexes
adhesionSpans(d)   # Vector of span morphisms
bags(d, true)      # Indexed: [(index, bag), ...]

# Functorial lift
d_lifted = 𝐃(F, d)                # Lift functor F to decomposition
d_lifted = 𝐃(F, d, CoDecomposition)  # Explicit type

# Decision
(answer, witness) = decide_sheaf_tree_shape(F, d)

# Colimit/Limit
global_obj = colimit(d)   # Glue bags together
dual_obj = limit(d)       # Dual construction
```

## Complexity

| Problem | Naive | StrDecomp | Width w |
|---------|-------|-----------|---------|
| k-Coloring | O(k^n) | O(k^w × n) | FPT |
| Hamiltonian | O(n!) | O(2^w × n) | FPT |
| Max Clique | O(2^n) | O(2^w × n) | FPT |

Runtime: **O(f(w) × n)** where w = treewidth, f = function of width only.

## Neighbor Awareness

| Position | Skill | Role |
|----------|-------|------|
| Left (-1) | `sheaf-cohomology` | Validates gluing obstructions |
| Right (+1) | `koopman-generator` | Generates dynamics from observables |

The **braided monoidal** structure ensures:
- Left neighbor provides obstruction detection (Čech cohomology)
- Right neighbor provides dynamical interpretation (Koopman lifting)
- Center (this skill) coordinates transport between local and global

## Commands

```bash
just strdecomp-test           # Run Julia test suite
just strdecomp-color k graph  # Test k-colorability
just strdecomp-walk seed      # Random walk with Gay.jl colors
just kbg-third                # Run Kleppmann-Bumpus-Gay simulation
```

## References

- [Bumpus et al. arXiv:2207.06091](https://arxiv.org/abs/2207.06091) - Sheaf-theoretic decision procedures
- [AlgebraicJulia/StructuredDecompositions.jl](https://github.com/AlgebraicJulia/StructuredDecompositions.jl)
- [DecidingSheaves.md](file:///Users/bob/ies/StructuredDecompositions.jl/docs/src/pages/DecidingSheaves.md)
- [str_decomps.jl](file:///Users/bob/ies/StructuredDecompositions.jl/src/decompositions/str_decomps.jl)
- [kleppmann_bumpus_gay_third.rb](file:///Users/bob/ies/music-topos/lib/kleppmann_bumpus_gay_third.rb)

---

**Status**: ✅ L4 Admissible (Typed, Documented, Compositional, Predicates + Neighbors)
**Trit**: 0 (ERGODIC)
**Date**: 2025-12-25

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
