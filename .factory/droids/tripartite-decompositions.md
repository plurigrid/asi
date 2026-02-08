---
name: tripartite-decompositions
description: GF(3)-balanced structured decompositions for parallel computation. Decomposes problems into MINUS/ERGODIC/PLUS components with sheaf-theoretic gluing. Use for FPT algorithms, skill allocation, or any 3-way parallel workload.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Tripartite Decompositions

**Trit**: 0 (ERGODIC - coordinates decomposition)  
**Foundation**: StructuredDecompositions.jl + GF(3) conservation  
**Principle**: Every problem decomposes into 3 parts summing to 0 mod 3

## Core Concept

A **tripartite decomposition** is a structured decomposition where:
1. The decomposition shape is a 3-clique (triangle)
2. Each bag is labeled with a trit ∈ {-1, 0, +1}
3. Adhesions preserve GF(3) conservation: Σ trits ≡ 0 (mod 3)

```
        MINUS (-1)
           ╱╲
          ╱  ╲
         ╱    ╲
        ╱  ⊗   ╲
       ╱________╲
 ERGODIC (0)   PLUS (+1)
 
 Conservation: (-1) + 0 + (+1) = 0 ✓
```

## Mathematical Foundation

### From StructuredDecompositions.jl

```julia
# A structured decomposition is a diagram d: ∫G → Span(C)
# where G is the decomposition shape and C is the target category

abstract type StructuredDecomposition{G, C, D} <: Diagram{id, C, D} end

struct StrDecomp{G, C, D} <: StructuredDecomposition{G, C, D}  
  decomp_shape ::G          # The shape (for tripartite: K₃)
  diagram      ::D          # The actual decomposition functor
  decomp_type  ::DecompType # Decomposition or CoDecomposition
  domain       ::C          # Source category
end
```

### Tripartite Extension

```julia
using StructuredDecompositions
using Catlab

# Define the tripartite shape: K₃ (complete graph on 3 vertices)
@present SchTripartite(FreeSchema) begin
    (Minus, Ergodic, Plus)::Ob
    
    # Adhesions (edges of K₃)
    me::Hom(Minus, Ergodic)
    ep::Hom(Ergodic, Plus)
    pm::Hom(Plus, Minus)
    
    # Trit attributes
    trit::Attr(Minus, Int)   # Always -1
    trit::Attr(Ergodic, Int) # Always 0
    trit::Attr(Plus, Int)    # Always +1
end

@acset_type TripartiteShape(SchTripartite)

# Tripartite decomposition with GF(3) verification
struct TripartiteDecomp{C, D} <: StructuredDecomposition{TripartiteShape, C, D}
    base::StrDecomp{TripartiteShape, C, D}
    
    function TripartiteDecomp(base::StrDecomp)
        # Verify GF(3) 