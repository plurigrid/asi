---
name: structured-decompositions
description: Functorial structured decompositions for compositional problem solving via sheaf-theoretic methods. Based on [AlgebraicJulia/StructuredDecompositions.jl](https://github.com/AlgebraicJulia/StructuredDecompositions.jl).
metadata:
  interface_ports:
  - References
  - Integration with
---
# Structured Decompositions Skill

Functorial structured decompositions for compositional problem solving via sheaf-theoretic methods. Based on [AlgebraicJulia/StructuredDecompositions.jl](https://github.com/AlgebraicJulia/StructuredDecompositions.jl).

## Core Principle: Decompose → Lift → Solve Locally → Reassemble

Hard global problems become tractable when:
1. **Decompose**: Break input into overlapping bags connected via adhesions
2. **Lift**: Apply functor 𝐃 to promote problem F: C → E to 𝐃F: 𝐃C → 𝐃E  
3. **Solve Locally**: Compute on bags, enforce consistency at adhesions via pullback
4. **Reassemble**: Sheaf condition guarantees global solution from local pieces

## Key Types

```julia
abstract type StructuredDecomposition{G, C, D} <: Diagram{id, C, D} end

@data DecompType begin
  Decomposition     # d: FG → Span C (contravariant)
  CoDecomposition   # d: FG → Cospan C^op (covariant)
end

struct StrDecomp{G, C, D} <: StructuredDecomposition{G, C, D}  
  decomp_shape ::G   # Shape graph (tree for tree decompositions)
  diagram      ::D   # Functor mapping shape to category C
  decomp_type  ::DecompType
  domain       ::C   # Category of elements ∫G
end
```

## Decomposition Anatomy

```
Bag₁ ←─[Adhesion₁₂]─→ Bag₂ ←─[Adhesion₂₃]─→ Bag₃

Each adhesion is a SPAN: Bag_i ← Apex → Bag_j
  - Apex encodes overlap/interface between bags
  - Morphisms are inclusion maps
```

## Essential Operations

| Function | Returns | Use Case |
|----------|---------|----------|
| `bags(d)` | Vertex objects | Get all pieces |
| `bags(d, true)` | `[(idx, obj)]` | Indexed for tracking |
| `adhesions(d)` | Edge apex objects | Get interfaces |
| `adhesionSpans(d)` | Span diagrams | Full overlap structure |

## Functorial Lifting (The Key Insight)

```julia
𝐃(f, d::StructuredDecomposition, t::DecompType)::StructuredDecomposition
```

If `F` encodes a computational problem, `𝐃(F, d)` promotes global computation to local computation on decomposition parts.

## Sheaf Decision Algorithm

```julia
decide_sheaf_tree_shape(f, d::StructuredDecomposition) → (Bool, Witness)
```

**Algorithm**:
1. Lift problem `f` to decomposition level: `𝐃(f, d, CoDecomposition)`
2. For each adhesion edge:
   - Extract cospan: `dx₁ → de ← dx₂`
   - Compute pullback cone with legs `l₁, l₂`
   - Project images: `im(l₁)`, `im(l₂)`
   - Replace apex with image intersection
3. If any bag empty → `(false, witness)`, else `(true, witness)`

## Adhesion Filter (Core Mechanism)

```julia
function adhesion_filter(i::Integer, d::StructuredDecomposition)
  # Fetch cospan dx₁ → de ← dx₂
  (csp, d_csp) = adhesionSpans(d, true)[i]
  
  # Pullback cone
  p_cone = pullback(d_csp)
  p_legs = legs(p_cone)
  
  # Project to images
  imgs = force.(map(f -> legs(image(f))[1], p_legs))
  
  # New cospan with filtered apex
  new_d_csp = force.(map(t -> compose(t...), zip(imgs, d_csp)))
  
  # Rebuild decomposition with filtered span
  StrDecomp(d.decomp_shape, new_diagram, d.decomp_type)
end
```

## Width-Parameterized Complexity

Problems encoded as sheaves solve in **FPT time** parameterized by decomposition width:
- **Treewidth k**: Largest bag has k+1 vertices
- **Complexity**: O(n · f(k)) where f depends only on width

## Pattern: Graph Coloring

```julia
struct Coloring; n::Int; end

function (c::Coloring)(graph::SymmetricGraph)
  FinSet(homomorphisms(graph, K(c.n)))
end

function (c::Coloring)(f::ACSetTransformation)
  FinFunction(λ -> compose(f, λ), c(codom(f)), c(dom(f)))
end

# Solve
graph = path_graph(SymmetricGraph, 100)
decomp = StrDecomp(graph)
result = decide_sheaf_tree_shape(skeleton ∘ Coloring(3), decomp)
```

## Connection to OlmoEarth Shared Protentions

| StructuredDecompositions | OlmoEarth | Shared Protention |
|--------------------------|-----------|-------------------|
| Bags | Modality tokens | Local view |
| Adhesions | Cross-attention | Interface |
| Sheaf condition | Instance contrastive | Agreement |
| Functorial lift 𝐃 | Frozen projection | Common ground |
| decide_sheaf_tree_shape | Decoding masked tokens | Prediction |

## When to Use

✅ **Good fit**:
- Decision problems on graphs with bounded treewidth
- Constraint satisfaction with sparse constraint graphs
- Compositional verification of distributed systems
- Multi-agent coordination with local observations

❌ **Poor fit**:
- Dense graphs (treewidth ≈ n)
- Problems without sheaf structure

## Local Source

`/Users/bob/ies/StructuredDecompositions.jl/`

---

## End-of-Skill Interface

## Integration with Other Skills

- **acsets-algebraic-databases**: Objects being decomposed are ACSets
- **gay-mcp**: GF(3) conservation across decomposition bags
- **world-hopping**: Decomposition as possible world navigation
- **bisimulation-game**: Sheaf consistency as bisimulation condition

## References

1. [Structured Decompositions Paper](https://arxiv.org/abs/2207.06091)
2. [Tree Decompositions](https://en.wikipedia.org/wiki/Tree_decomposition)
3. [Sheaf Theory](https://en.wikipedia.org/wiki/Sheaf_(mathematics))


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
