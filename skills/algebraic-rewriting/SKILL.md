---
name: algebraic-rewriting
description: Category-theoretic graph rewriting with DPO, SPO, and SqPO pushouts for C-Sets. Declarative transformation of acset data structures.
version: 1.0.0
---


# Algebraic Rewriting

## Overview

**AlgebraicRewriting.jl** is a Julia library for performing category-theoretic rewrites over C-Sets and other Catlab.jl data structures.

## Rewriting Approaches

| Type | Description | Use Case |
|------|-------------|----------|
| **DPO** | Double Pushout | Safe deletion (no dangling edges) |
| **SPO** | Single Pushout | Greedy deletion |
| **SqPO** | Sesqui-Pushout | Cloning + deletion |

## Core Concepts

### Rewrite Rules

A rewrite rule consists of:
- **L** (left) - Pattern to match
- **K** (interface) - What to preserve
- **R** (right) - Replacement pattern

```julia
using AlgebraicRewriting

# Define a rule: merge two vertices
L = @acset Graph begin V=2; E=1; src=[1]; tgt=[2] end
K = @acset Graph begin V=1 end
R = @acset Graph begin V=1 end

rule = Rule(L, K, R)
```

### Apply Rewriting

```julia
G = @acset Graph begin
    V = 4
    E = 3
    src = [1, 2, 3]
    tgt = [2, 3, 4]
end

# Find matches and rewrite
matches = homomorphisms(L, G)
G′ = rewrite(rule, G, matches[1])
```

## Double Pushout (DPO)

```
    L ←──l── K ──r──→ R
    │         │         │
    m         k         m*
    │         │         │
    ▼         ▼         ▼
    G ←────── D ──────→ H
```

Both squares are **pushouts**. The context D ensures no "dangling edges" after deletion.

### DPO Existence Conditions (Gluing Condition)

Given a match m : L → G, the pushout complement D exists iff:

1. **Dangling condition**: No edge in G \ m(L) is incident to a node in m(L) \ m(K).
   Intuitively: deleting L \ K must not leave edges dangling.

2. **Identification condition**: If m(x) = m(y) for x, y ∈ L, then x, y ∈ K.
   Intuitively: if two elements are identified by the match, both must survive.

```julia
# DPO rewrite (default in AlgebraicRewriting.jl)
using AlgebraicRewriting, Catlab

L = @acset Graph begin V=2; E=1; src=[1]; tgt=[2] end
K = @acset Graph begin V=2 end                      # keep both vertices
R = @acset Graph begin V=2; E=1; src=[2]; tgt=[1] end  # reverse the edge

rule = Rule(homomorphism(K, L), homomorphism(K, R))

G = @acset Graph begin V=3; E=2; src=[1,2]; tgt=[2,3] end
m = homomorphism(L, G)
H = rewrite(rule, G)  # edge 1→2 becomes 2→1
```

## Single Pushout (SPO)

SPO uses a **single pushout** in the category of partial morphisms:

```
    L ──r──→ R
    │         │
    m         m*
    │         │
    ▼         ▼
    G ──────→ H
```

No gluing condition needed — dangling edges are deleted automatically.

```julia
# SPO rewrite: greedy deletion
rule_spo = Rule(homomorphism(K, L), homomorphism(K, R); type=:SPO)
H = rewrite(rule_spo, G)  # dangling edges silently removed
```

## Sesqui-Pushout (SqPO)

SqPO supports **cloning** via the **final pullback complement**:

```
    L ←──l── K ──r──→ R
    │         │         │
    m         ⌐         m*
    │      (FPC)        │
    ▼         ▼         ▼
    G ←────── D ──────→ H
```

The left square is a final pullback complement (FPC), the right is a pushout.

```julia
# SqPO clone: one vertex becomes two
L = @acset Graph begin V=1 end
K = @acset Graph begin V=1 end
R = @acset Graph begin V=2 end

clone_rule = Rule(homomorphism(K, L), homomorphism(K, R); type=:SqPO)
# Applying this to a graph clones the matched vertex AND all incident edges
```

### Comparison Table

| Property | DPO | SPO | SqPO |
|----------|-----|-----|------|
| Deletion | Safe (gluing condition) | Greedy | Safe |
| Cloning | No | No | Yes (FPC) |
| Pushout type | Double | Single (partial) | Sesqui (FPC + PO) |
| Confluence | Conditional (critical pairs) | Harder to ensure | Conditional |
| Category requirement | Adhesive | Has partial morphisms | Has FPCs |
| Use when | Default | Cleanup/garbage collection | Gene duplication, copying |

## 5. Adhesive Categories

### 5.1 Definition

A category C is **adhesive** if:
1. C has all pullbacks
2. C has pushouts along monomorphisms
3. Pushouts along monos are **van Kampen (VK) squares**

**Van Kampen condition**: A pushout square

```
    A ──→ B
    │      │
    ↓      ↓
    C ──→ D
```

is VK if for any commutative cube with this as the bottom face,
where the back faces are pullbacks, the top face is a pushout
iff the front faces are pullbacks.

### 5.2 Why Adhesive Matters

Adhesive categories guarantee:
- **Pushout complement uniqueness**: D in DPO is unique (when it exists)
- **Local Church-Rosser**: Parallel independent rewrites commute
- **Concurrency theorem**: Sequential independent rewrites can be done in one step
- **Embedding theorem**: Rules preserve subobject structure

### 5.3 Examples

| Category | Adhesive? | Notes |
|----------|-----------|-------|
| **Set** | Yes | Trivial (discrete graphs) |
| **Graph** | Yes | Standard graph rewriting |
| **C-Set** (presheaves) | Yes | **The main one for AlgebraicRewriting.jl** |
| **Typed Graph** | Yes | Graphs with node/edge types |
| **Hypergraph** | Yes | Multi-endpoint edges |
| **Petri nets** | Quasi-adhesive | Weaker VK condition |

C-Sets (functors C → Set for a small category C) are the workhorse:
every schema in Catlab.jl defines a C-Set category, and they are all adhesive.

## 6. Negative Application Conditions (NACs)

A **NAC** forbids a rule from applying when a larger pattern is present:

```julia
# Rule: delete isolated vertex (no incident edges)
L = @acset Graph begin V=1 end
K = @acset Graph begin end         # empty
R = @acset Graph begin end         # empty

# NAC: don't apply if vertex has an edge
NAC = @acset Graph begin V=1; E=1; src=[1]; tgt=[1] end

rule = Rule(homomorphism(K, L), homomorphism(K, R);
            ac=[AppCond(homomorphism(L, NAC), false)])  # false = negative
```

NACs are essential for:
- **Termination**: Prevent rules from applying to their own output
- **Safety**: Ensure structural invariants are maintained
- **Specificity**: Match only the intended pattern, not superpatterns

### PACs (Positive Application Conditions)

Dually, PACs **require** a larger pattern to be present:

```julia
# Only delete a vertex if it has a self-loop
PAC = @acset Graph begin V=1; E=1; src=[1]; tgt=[1] end
rule = Rule(homomorphism(K, L), homomorphism(K, R);
            ac=[AppCond(homomorphism(L, PAC), true)])  # true = positive
```

## 7. Critical Pair Analysis

### 7.1 Overlaps

Two rules r₁ : L₁ ← K₁ → R₁ and r₂ : L₂ ← K₂ → R₂ have a **critical pair**
when their left-hand sides overlap non-trivially:

```
Overlap = jointly surjective pair (L₁ → S ← L₂)
```

For each overlap S:
1. Apply r₁ to S via the L₁ match → get H₁
2. Apply r₂ to S via the L₂ match → get H₂
3. The pair (H₁, H₂) is a **critical pair**

### 7.2 Joinability

A critical pair (H₁, H₂) is **joinable** if ∃ H₃ such that H₁ →* H₃ ←* H₂.

```
        S
       / \
  r₁ /   \ r₂
    /     \
   H₁     H₂
    \     /
     \   /  (joinable?)
      \ /
       H₃
```

### 7.3 Local Confluence Theorem (Adhesive Categories)

**Theorem** (Ehrig et al. 2006): In an adhesive category, a terminating
rewriting system is confluent iff all critical pairs are joinable.

This is the **Critical Pair Lemma** for graph transformation — the analogue
of the Knuth-Bendix critical pair theorem for term rewriting.

```julia
# In AlgebraicRewriting.jl:
using AlgebraicRewriting: critical_pairs

cps = critical_pairs(rule1, rule2)
for (h1, h2) in cps
    @assert is_joinable(h1, h2, [rule1, rule2])
end
```

### 7.4 Parallel Independence

Two matches m₁ : L₁ → G, m₂ : L₂ → G are **parallel independent** if:
- m₁(L₁ \ K₁) ∩ m₂(L₂) = ∅, AND
- m₂(L₂ \ K₂) ∩ m₁(L₁) = ∅

Parallel independent rewrites commute (Local Church-Rosser for adhesive categories).

## 8. Termination

### 8.1 Weighted Type Graph

Assign weights w : Types → ℕ to node/edge types in the schema:

```julia
# Termination measure: total weight of the ACSet
function weight(G::ACSet, w::Dict)
    sum(w[type] * nparts(G, type) for type in ob(acset_schema(G)))
end

# Rule terminates if: weight(L) > weight(R) for all matches
```

### 8.2 Layered Termination

When rules don't all decrease the same measure, use a **lexicographic ordering**:

```
(w₁(G), w₂(G), w₃(G), ...)   >_lex   (w₁(H), w₂(H), w₃(H), ...)
```

### 8.3 Completion (Knuth-Bendix for Graphs)

Given equations L₁ = R₁, ..., Lₙ = Rₙ, attempt to orient into rules:

1. Orient each equation Lᵢ → Rᵢ using the termination ordering
2. Compute all critical pairs
3. For non-joinable critical pairs, add new rules
4. Repeat until convergent (or fail)

## 9. String Diagram Rewrite Rules

### 9.1 Diagrams as C-Sets

String diagrams are C-Sets over the schema:

```julia
@present SchStringDiagram(FreeSchema) begin
    Box::Ob           # morphisms
    Wire::Ob          # objects/types
    InPort::Ob        # input ports
    OutPort::Ob       # output ports
    box_in::Hom(InPort, Box)
    box_out::Hom(OutPort, Box)
    wire_src::Hom(Wire, OutPort)
    wire_tgt::Hom(Wire, InPort)
    port_type::Attr(InPort, Symbol)
    port_type::Attr(OutPort, Symbol)
end
```

### 9.2 Monoidal Structure as Rewriting

| String diagram operation | Rewriting operation |
|-------------------------|---------------------|
| Sequential composition (;) | Merge two box-wire patterns |
| Tensor product (⊗) | Disjoint union of C-Sets |
| Identity wire | Single wire, no boxes |
| Symmetry (swap) | Wire crossing pattern |
| Trace (feedback) | Wire connecting output to input |

### 9.3 Example: Composing String Diagrams via DPO

```julia
# Rule: compose two sequential boxes into one
L = @acset SchStringDiagram begin
    Box=2; Wire=1; InPort=2; OutPort=2
    box_in=[1,2]; box_out=[1,2]
    wire_src=[2]; wire_tgt=[2]  # wire from box1.out to box2.in
end

K = @acset SchStringDiagram begin
    InPort=1; OutPort=1  # preserve external ports
end

R = @acset SchStringDiagram begin
    Box=1; InPort=1; OutPort=1
    box_in=[1]; box_out=[1]
end

compose_rule = Rule(homomorphism(K, L), homomorphism(K, R))
```

## 10. Protocol Binding

```yaml
skill_binding:
  skill_name: algebraic-rewriting
  layer: 2  # Rewriting Engine
  trit: +1  # PLUS (generation — produces rewritten structures)
  category:
    name: CSet
    monoidal: true    # disjoint union = tensor
    symmetric: true   # permutation of components
    compact: false
    traced: false
    adhesive: true    # C-Sets are adhesive!
    enrichment: null
  rules: "dynamic — user-defined via Rule constructor"
  functors:
    - source: CSet(SchGraph)
      target: CSet(SchStringDiagram)   # embedding
    - source: CSet
      target: Graph                     # forgetful
```

## Documentation

- [Full Documentation](https://algebraicjulia.github.io/AlgebraicRewriting.jl/dev/)
- [Brown 2022](https://arxiv.org/abs/2111.03784) - Theoretical foundation
- [Ehrig et al. 2006](https://link.springer.com/book/10.1007/3-540-31188-2) - Fundamentals of AGT

## Repository

- **Source**: plurigrid/AlgebraicRewriting.jl (fork of AlgebraicJulia)
- **Seed**: `0xabfca37b6b4bc699`
- **Index**: 496/1055
- **Color**: #c25d0b

## GF(3) Triad

```
algebraic-rewriting (+1) ⊗ acsets-hatchery (0) ⊗ interaction-nets (-1) = 0 ✓
algebraic-rewriting (+1) ⊗ categorical-rewriting (0) ⊗ zx-calculus (-1) = 0 ✓
```

## Related Skills

- `acsets-hatchery` - ACSet data structures (Catlab.jl)
- `topos-adhesive-rewriting` - Adhesive categories (theory)
- `interaction-nets` - Alternative rewriting formalism
- `world-a` - AlgebraicJulia ecosystem
- `string-diagram-rewriting-protocol` - Kernel protocol (this skill is Layer 2)

## Literature

1. **Ehrig, Ehrig, Prange, Taentzer (2006)** - *Fundamentals of Algebraic Graph Transformation* Springer
2. **Lack & Sobocinski (2004)** - "Adhesive categories" FOSSACS
3. **Brown (2022)** - "Categorical Data Structures for Technical Computing" (AlgebraicJulia)
4. **Patterson et al. (2022)** - "Categorical data structures for technical computing" Compositionality
5. **Corradini et al. (1997)** - "Algebraic approaches to graph transformation" Handbook of Graph Grammars
6. **Löwe (1993)** - "Algebraic approach to single-pushout graph transformation" TCS
7. **Corradini et al. (2006)** - "Sesqui-pushout rewriting" ICGT

## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 4. Pattern Matching

**Concepts**: pattern matching, unification, match combinators — directly analogous
to finding homomorphisms L → G in DPO rewriting.

### GF(3) Balanced Triad

```
algebraic-rewriting (+1) + SDF.Ch4 (+1) + zx-calculus (-1) = +1 ≡ ...
```

Corrected triad:
```
algebraic-rewriting (+1) + SDF.Ch7.propagators (0) + interaction-nets (-1) = 0 ✓
```

**Skill Trit**: +1 (PLUS - generation)

### Secondary Chapters

- Ch3: Variations on Arithmetic — generic operations over different ACSet schemas
- Ch9: Generic Procedures — multi-dispatch for rewrite rule selection
- Ch7: Propagators — constraint propagation as rewriting fixpoint
- Ch10: Adventure Game — synthesis of rewriting techniques

### Connection Pattern

Pattern matching finds homomorphisms. Rewriting applies the matched rule.
AlgebraicRewriting.jl's `homomorphisms(L, G)` IS pattern matching in the
category of C-Sets.
