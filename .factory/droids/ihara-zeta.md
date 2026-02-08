---
name: ihara-zeta
description: "Ihara zeta function for graphs: non-backtracking walks, prime cycles, and spectral analysis via det(I - uB)."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Ihara Zeta Function Skill

> *"The Ihara zeta function encodes all non-backtracking closed walks - the 'prime cycles' of a graph."*

## Overview

The Ihara zeta function generalizes the Riemann zeta function to graphs:

1. **Prime cycles** - Non-backtracking closed walks (graph analog of primes)
2. **Determinant formula** - ζ_G(u)^{-1} = det(I - uB) relation
3. **Ramanujan connection** - Riemann Hypothesis analog for graphs
4. **Non-backtracking matrix** - Central object for spectral clustering

## Definition

### Ihara Zeta Function

For a graph G, the **Ihara zeta function** is:

```
ζ_G(u) = ∏_{[C]} (1 - u^{|C|})^{-1}
```

where:
- Product is over equivalence classes [C] of **primitive** closed non-backtracking walks
- |C| is the length of the cycle
- Primitive = not a power of a shorter cycle

### Non-Backtracking Walk

A walk `v₀ → v₁ → v₂ → ... → vₖ` is **non-backtracking** if:

```
vᵢ₊₁ ≠ vᵢ₋₁  for all i
```

(Never immediately return to the previous vertex)

## The Determinant Formula

### Bass-Hashimoto Formula

```
ζ_G(u)^{-1} = (1 - u²)^{|E| - |V|} · det(I - uB)
```

where **B** is the non-backtracking matrix.

### Non-Backtracking Matrix

Indexed by **directed edges** (e, f) where head(e) = tail(f) and e ≠ f⁻¹:

```julia
function non_backtracking_matrix(G)
    # Directed edges: 2|E| entries
    directed_edges = [(u,v) for (u,v) in edges(G) 
                      for dir in [(u,v), (v,u)]]
    
    m = length(directed_edges)
    B = zeros(m, m)
    
    for (i, e) in enumerate(directed_edges)
        for (j, f) in enumerate(directed_edges)
            # e = (a→b), f = (c→d)
            # Connect if b = c AND a ≠ d (non-backtracking)
            if e[2] == f[1] && e[1] != f[2]
                B[i, j] = 1
            end
        end
    end
    
    return B
end
```

## Prime Cycles and Möbius

### Connection to Number Theory

| Number Theory | Graph Theory |
|---------------|--------------|
| Prime number p | Prime cycle C |
| log p | Length |C| |
| Riem