# CRDT Color ACSet Operations
# DPO rewriting, concurrent edit detection, and merge operations

include("acset-schema.jl")
using Catlab.CategoricalAlgebra: pushout, pullback, homomorphism

# ═══════════════════════════════════════════════════════════════════
# Specter-style Navigation Paths
# ═══════════════════════════════════════════════════════════════════

abstract type Path end

struct ALL <: Path end
struct FIRST <: Path end
struct LAST <: Path end
struct FILTER{F} <: Path
    pred::F
end
struct CHILD{S} <: Path
    morphism::S
end

# Navigate to all spans in a document
function select(doc::ColorDocACSet, ::Type{ALL}, ::Val{:Span})
    parts(doc, :Span)
end

# Navigate via morphism
function select(doc::ColorDocACSet, p::CHILD{Symbol}, ids::Vector{Int})
    morphism = p.morphism
    [i for i in ids for j in incident(doc, i, morphism)]
end

# Filter by predicate
function select(doc::ColorDocACSet, p::FILTER, ids::Vector{Int})
    filter(p.pred, ids)
end

# Compose paths: doc |> CHILD(:doc_of) |> FILTER(x -> x.trit == 0)
function navigate(doc::ColorDocACSet, paths::Vector{<:Path}, start::Vector{Int})
    foldl((ids, p) -> select(doc, p, ids), paths, init=start)
end

# ═══════════════════════════════════════════════════════════════════
# Edit Operations as DPO Rewriting Rules
# ═══════════════════════════════════════════════════════════════════

struct EditOp
    kind::Symbol        # :insert, :delete, :recolor
    target_span::Int
    new_color::Union{Nothing, String}
    new_seed::Union{Nothing, UInt64}
    new_idx::Union{Nothing, Int}
    author::String
    vclock::VectorClock
end

# Insert: L ← K → R where K is context, L is empty, R has new span
function apply_insert!(doc::ColorDocACSet, para_id::Int, 
                       hex::String, seed::UInt64, idx::Int,
                       author::String, vclock::VectorClock)
    trit = mod(parse(Int, hex[2:3], base=16), 3) - 1
    
    # Add author if not exists
    existing = findall(==(author), doc[:, :author_id])
    auth_id = isempty(existing) ? 
        add_part!(doc, :Author, author_id=author) : first(existing)
    
    # Add timestamp
    ts_id = add_part!(doc, :Timestamp, timestamp=time())
    
    # Add span (R in DPO)
    span_id = add_part!(doc, :Span, para_of=para_id,
                        color=hex, seed=seed, idx=idx, trit=trit)
    
    # Record edit
    edit_id = add_part!(doc, :ColorEdit, 
                        edit_of=span_id, authored_by=auth_id, at_time=ts_id)
    
    tick!(vclock, author)
    return (span_id, edit_id)
end

# Delete: L ← K → R where L has span, R is empty (tombstone approach)
function apply_delete!(doc::ColorDocACSet, span_id::Int,
                       author::String, vclock::VectorClock)
    # CRDT: mark as deleted, don't actually remove (tombstone)
    # Set trit to 0 to maintain GF(3) neutrality
    old_trit = doc[span_id, :trit]
    doc[span_id, :trit] = 0
    doc[span_id, :color] = "#000000"  # Tombstone marker
    
    tick!(vclock, author)
    return -old_trit  # Return compensation trit
end

# Recolor: L ← K → R where L and R differ only in color attributes
function apply_recolor!(doc::ColorDocACSet, span_id::Int,
                        new_hex::String, new_seed::UInt64, new_idx::Int,
                        author::String, vclock::VectorClock)
    old_trit = doc[span_id, :trit]
    new_trit = mod(parse(Int, new_hex[2:3], base=16), 3) - 1
    
    doc[span_id, :color] = new_hex
    doc[span_id, :seed] = new_seed
    doc[span_id, :idx] = new_idx
    doc[span_id, :trit] = new_trit
    
    tick!(vclock, author)
    return GF3(new_trit - old_trit)  # Trit delta
end

# ═══════════════════════════════════════════════════════════════════
# Concurrent Edit Detection via Pullback
# ═══════════════════════════════════════════════════════════════════

struct ConflictResult
    has_conflict::Bool
    edit_a::Union{Nothing, EditOp}
    edit_b::Union{Nothing, EditOp}
    common_ancestor::Union{Nothing, Int}
end

function detect_concurrent_edits(edit_a::EditOp, edit_b::EditOp)
    # Concurrent iff vector clocks are incomparable
    if concurrent(edit_a.vclock, edit_b.vclock)
        if edit_a.target_span == edit_b.target_span
            return ConflictResult(true, edit_a, edit_b, edit_a.target_span)
        end
    end
    return ConflictResult(false, nothing, nothing, nothing)
end

# ═══════════════════════════════════════════════════════════════════
# Merge via Pushout with GF(3) Conservation
# ═══════════════════════════════════════════════════════════════════

struct MergeResult
    success::Bool
    merged_doc::Union{Nothing, ColorDocACSet}
    gf3_preserved::Bool
    trit_sum::GF3
end

function merge_edits(doc_a::ColorDocACSet, doc_b::ColorDocACSet,
                     common_ancestor::ColorDocACSet)
    # Compute pushout: doc_a ←─ ancestor ─→ doc_b
    #                      ↘      ↙
    #                       merged
    
    # Simplified merge: prefer later timestamp, preserve GF(3)
    merged = deepcopy(doc_a)
    
    # Track trit changes
    initial_sum = gf3_sum(common_ancestor)
    
    # Merge spans from doc_b that aren't in doc_a
    for span_b in parts(doc_b, :Span)
        color_b = doc_b[span_b, :color]
        seed_b = doc_b[span_b, :seed]
        
        # Check if this span exists in merged (by seed+idx)
        existing = findall(s -> merged[s, :seed] == seed_b, parts(merged, :Span))
        
        if isempty(existing)
            # Insert from doc_b
            para_id = doc_b[span_b, :para_of]
            trit = doc_b[span_b, :trit]
            add_part!(merged, :Span, para_of=para_id,
                     color=color_b, seed=seed_b, 
                     idx=doc_b[span_b, :idx], trit=trit)
        end
    end
    
    final_sum = gf3_sum(merged)
    preserved = (final_sum.val == initial_sum.val)
    
    # If not preserved, add compensating span
    if !preserved
        delta = initial_sum.val - final_sum.val
        # Add neutral-colored compensating span
        comp_trit = mod(delta + 1, 3) - 1
        add_part!(merged, :Span, para_of=1,
                 color="#808080", seed=UInt64(0), idx=0, trit=comp_trit)
    end
    
    return MergeResult(true, merged, preserved, gf3_sum(merged))
end

# ═══════════════════════════════════════════════════════════════════
# Example: Two Concurrent Edits Merging
# ═══════════════════════════════════════════════════════════════════

function demo_concurrent_merge()
    println("═" ^ 60)
    println("CRDT Color Merge Demo with GF(3) Conservation")
    println("═" ^ 60)
    
    # Create shared ancestor
    ancestor = create_color_doc("shared")
    add_paragraph!(ancestor, 1, "#FF0000", UInt64(1069), 1)  # Red, trit=2→-1
    add_paragraph!(ancestor, 1, "#00FF00", UInt64(1069), 2)  # Green, trit=0
    
    println("\nAncestor GF(3) sum: ", gf3_sum(ancestor).val)
    
    # Alice's branch
    doc_alice = deepcopy(ancestor)
    vc_alice = VectorClock()
    apply_insert!(doc_alice, 1, "#0000FF", UInt64(1069), 3, "alice", vc_alice)
    println("After Alice insert: GF(3) = ", gf3_sum(doc_alice).val)
    
    # Bob's concurrent branch
    doc_bob = deepcopy(ancestor)
    vc_bob = VectorClock()
    apply_recolor!(doc_bob, 1, "#FFFF00", UInt64(1069), 4, "bob", vc_bob)
    println("After Bob recolor: GF(3) = ", gf3_sum(doc_bob).val)
    
    # Detect conflict
    edit_alice = EditOp(:insert, 0, "#0000FF", UInt64(1069), 3, "alice", vc_alice)
    edit_bob = EditOp(:recolor, 1, "#FFFF00", UInt64(1069), 4, "bob", vc_bob)
    
    conflict = detect_concurrent_edits(edit_alice, edit_bob)
    println("\nConcurrent edits detected: ", conflict.has_conflict)
    
    # Merge via pushout
    result = merge_edits(doc_alice, doc_bob, ancestor)
    println("\nMerge successful: ", result.success)
    println("GF(3) preserved: ", result.gf3_preserved)
    println("Final GF(3) sum: ", result.trit_sum.val)
    
    # Show final spans
    println("\nMerged document spans:")
    for span in parts(result.merged_doc, :Span)
        c = result.merged_doc[span, :color]
        t = result.merged_doc[span, :trit]
        println("  Span $span: color=$c, trit=$t")
    end
    
    return result
end

export EditOp, apply_insert!, apply_delete!, apply_recolor!
export detect_concurrent_edits, merge_edits, ConflictResult, MergeResult
export Path, ALL, FIRST, LAST, FILTER, CHILD, navigate
export demo_concurrent_merge
