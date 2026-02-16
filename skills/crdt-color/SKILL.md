# CRDT Color Skill

> **Trit**: 0 (ERGODIC) - Coordinates between verification (-1) and generation (+1)

Color-aware CRDT operations with GF(3) conservation, Narya proofs, ACSet schemas, and Bumpus narrative sheaves.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    CRDT Color Skill                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐       │
│  │ Narya/Cat#   │    │  Eg-walker   │    │   Bumpus     │       │
│  │ Proofs (-1)  │◄──►│  DAG (0)     │◄──►│ Sheaves (+1) │       │
│  └──────────────┘    └──────────────┘    └──────────────┘       │
│         │                   │                   │                │
│         │            ┌──────┴──────┐            │                │
│         │            │   ACSet     │            │                │
│         └────────────│  Schema     │────────────┘                │
│                      └──────┬──────┘                             │
│                             ▼                                    │
│                    ┌──────────────┐                              │
│                    │  Gay.jl RNG  │                              │
│                    │  SplitMix64  │                              │
│                    └──────────────┘                              │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## Eg-walker Integration (Gentle & Kleppmann, EuroSys 2025)

**Core Innovation**: Simple indices + DAG replay instead of complex CRDT metadata.

```julia
# Traditional CRDTs store complex position descriptors
# Eg-walker stores simple index at execution time
struct ColorOp
    index::Int          # Simple index (not CRDT metadata!)
    color_hex::String   # Gay.jl color
    trit::Int8          # GF(3) assignment
    parent_ids::Vector{UInt64}  # DAG edges
end

# Merge via replay: O(k log n) instead of O(n²)
merged = merge_branches(alice_state, bob_state)
```

### Complexity Comparison

| Metric | Traditional CRDT | OT | Eg-walker |
|--------|------------------|-----|-----------|
| Memory/op | O(n) | O(1) | **O(1)** |
| Doc load | O(n²) | O(n) | **O(n log n)** |
| Merge | O(k log n) | O(n²) | **O(k log n)** |
| Tombstones | Unbounded | N/A | **None (replay)** |

### GF(3) + Eg-walker

- Each ColorOp carries trit: O(1) overhead
- Merge verification: O(k) path traversal  
- Rebalancing: O(1) amortized (single compensating op)

## GF(3) Conservation Law

All operations maintain: `Σ trits ≡ 0 (mod 3)`

| Operation | Trit | Effect |
|-----------|------|--------|
| Restriction | -1 | Shrink time window |
| Pullback (Merge) | 0 | Combine concurrent edits |
| Extension | +1 | Expand time window |

**Triad balance**: `restriction(-1) ⊕ pullback(0) ⊕ extension(+1) = 0 ✓`

## Core Types

```julia
# ColorEdit: Atomic edit with GF(3) trit
struct ColorEdit
    seed::UInt64      # Gay.jl seed
    idx::Int          # Color index
    color::RGB        # Computed color
    trit::Int8        # GF(3) ∈ {-1, 0, +1}
    timestamp::Nat    # Lamport timestamp
end

# Observational Bridge: hex equality → trit equality
ColorBridge : e1.hex == e2.hex → e1.trit == e2.trit

# Merge: LWW with deterministic tiebreaker
merge(e1, e2) = e1.timestamp > e2.timestamp ? e1 : 
                e1.timestamp < e2.timestamp ? e2 :
                e1.hex < e2.hex ? e1 : e2
```

## Proof Obligations (Narya)

1. **merge_comm**: `merge(e1, e2) = merge(e2, e1)`
2. **merge_assoc**: `merge(merge(e1, e2), e3) = merge(e1, merge(e2, e3))`
3. **merge_idem**: `merge(e, e) = e`
4. **gf3_conserved**: Winner-takes-all preserves trit
5. **replica_conservation**: Merged logs maintain `Σ trits ≡ 0 (mod 3)`

## ACSet Schema

```julia
@present SchColorDoc(FreeSchema) begin
    # Objects
    Document::Ob
    Paragraph::Ob  
    Span::Ob
    ColorEdit::Ob
    Author::Ob
    Timestamp::Ob
    
    # Morphisms
    parent::Hom(Paragraph, Document)
    in_para::Hom(Span, Paragraph)
    edit_of::Hom(ColorEdit, Span)
    authored_by::Hom(ColorEdit, Author)
    at_time::Hom(ColorEdit, Timestamp)
    
    # Attributes
    color::Attr(Span, RGB)
    seed::Attr(ColorEdit, UInt64)
    idx::Attr(ColorEdit, Int)
    trit::Attr(Span, GF3)
end
```

## Bumpus Sheaf Operations

```julia
# Time category with intervals
struct TimeInterval
    start::Nat
    stop::Nat
end

# Narrative sheaf: intervals → document states
struct NarrativeSheaf
    sections::Dict{TimeInterval, ColorDocument}
end

# Sheaf condition via pullback
F([a,b]) = F([a,p]) ×_{F([p,p])} F([p,b])

# Pullback merge for concurrent edits
function pullback_merge(left::ColorDocument, right::ColorDocument, 
                        ancestor::ColorDocument)
    merged = fibered_product(left, right, ancestor)
    @assert gf3_sum(merged) % 3 == 0 "GF(3) violation"
    merged
end
```

## Adhesion Filter (FPT)

Tree decomposition yields **O(3^w · n)** complexity:
- `w` = treewidth of edit dependency graph
- `n` = number of edits
- Polynomial in `n` for bounded treewidth

## Usage

```julia
using CRDTColor

# Create document with seed
doc = ColorDocument(seed=1069)

# Add colored span
span = add_span!(doc, "Hello", color_at(1069, 1))

# Concurrent edits
edit1 = recolor!(doc, span, color_at(1069, 2), author=:alice)
edit2 = recolor!(doc, span, color_at(1069, 3), author=:bob)

# Merge via pullback
merged = pullback_merge(edit1, edit2, ancestor=span)

# Verify GF(3) conservation
@assert gf3_balanced(merged)
```

## Skill Composition

```
narya-proofs (-1) ⊗ crdt-color (0) ⊗ bumpus-narratives (+1) = 0 ✓
acsets (-1) ⊗ crdt-color (0) ⊗ gay-mcp (+1) = 0 ✓
structured-decomp (-1) ⊗ crdt-color (0) ⊗ world-hopping (+1) = 0 ✓
```

## Files

- [narya-tracking.md](narya-tracking.md) - Type theory and proof obligations
- [acset-schema.jl](acset-schema.jl) - ACSet schema definition
- [acset-operations.jl](acset-operations.jl) - DPO rewriting and Specter paths
- [bumpus-sheaf.jl](bumpus-sheaf.jl) - Narrative sheaf implementation
- [gf3-conservation.jl](gf3-conservation.jl) - GF(3) invariant proofs
- [adhesion-filter.jl](adhesion-filter.jl) - FPT merge algorithm

## References

- [Bumpus et al. - Sheaves on Time Categories](https://arxiv.org/abs/2312.xxxxx)
- [Gay.jl - Deterministic Color Generation](https://github.com/plurigrid/Gay.jl)
- [AlgebraicJulia - ACSets](https://github.com/AlgebraicJulia/ACSets.jl)
- [Narya - Higher Observational Type Theory](https://github.com/mikeshulman/narya)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
