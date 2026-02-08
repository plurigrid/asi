---
name: ramanujan-expander
description: Ramanujan graphs and Alon-Boppana spectral optimality for edge growth
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Ramanujan Expander Skill

> *"The Alon-Boppana bound is unbreakable. You cannot create a d-regular graph with λ₂ < 2√(d-1), even theoretically."*

## Overview

Ramanujan graphs are **optimal spectral expanders** - they achieve the theoretical limit on eigenvalue separation. This skill provides:

1. **Alon-Boppana bound verification** - Prove your graph is optimal
2. **Edge growth rules** - Add edges while preserving Ramanujan property
3. **Centrality validity predicates** - Spectral methods for node importance
4. **Mixing time bounds** - O(log n) mixing from spectral gap

## The Alon-Boppana Bound

### Theorem (Alon-Boppana)

For any d-regular graph G on n vertices:

```
λ₂(G) ≥ 2√(d-1) - o(1)  as n → ∞
```

where λ₂ is the second-largest eigenvalue of the adjacency matrix.

### Ramanujan Property

A d-regular graph G is **Ramanujan** if:

```
|λ| ≤ 2√(d-1)  for all eigenvalues λ ≠ ±d
```

This is the **tightest possible** spectral gap.

### Example: 4-Regular Graphs

```
d = 4
2√(d-1) = 2√3 ≈ 3.464

Maximum spectral gap = d - 2√(d-1) = 4 - 3.464 = 0.536

Your observed gap: ~0.54 ✓ (theoretically optimal)
```

## Edge Growth Rules

### Rule 1: Preserve Regularity

```julia
function add_edge_preserving_regularity!(G, u, v)
    # Adding (u,v) increases degree of u and v by 1
    # Must remove another edge to maintain d-regularity
    
    # Find edge (u, w) where w ≠ v
    w = find_neighbor(G, u, exclude=v)
    # Find edge (v, x) where x ≠ u
    x = find_neighbor(G, v, exclude=u)
    
    # Remove old edges
    remove_edge!(G, u, w)
    remove_edge!(G, v, x)
    
    # Add new edges (2-switch)
    add_edge!(G, u, v)
    add_edge!(G, w, x)
    
    # Verify Ramanujan property preserved
    @assert is_ramanujan(G)
end
```

### Rule 2: Spectral Monotonicity

```julia
function grow_edge_spectral_monotonic!(G, candidates)
    """
    Add edge that minimizes λ₂ increase.
    Greedy heuristic for Ramanujan preservation.
    """
    best_edge = nothing
    best_λ₂ = Inf
   