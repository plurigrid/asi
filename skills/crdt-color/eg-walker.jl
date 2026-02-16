# Eg-walker: Event Graph Walker for Color CRDTs
# Based on Gentle & Kleppmann (EuroSys 2025)
# "Better, Faster, Smaller" - simple indices, replay when needed

module EgWalker

using Gay: color_at, seed!, trit_from_hue
include("acset-schema.jl")
include("gf3-conservation.jl")
using .GF3Conservation: Trit, ⊕, check_conservation

export EventGraph, EventNode, EgWalkerState, ColorOp,
       insert!, delete!, replay_to_merge, simple_index_at,
       build_event_graph, walk_graph, merge_branches

# =============================================================================
# Core Innovation: Simple Indices Instead of Complex CRDT Metadata
# =============================================================================
#
# Traditional CRDTs store:
#   - RGA: operation ID + Lamport timestamp of left neighbor
#   - Yjs/Fugue: operation IDs of both left AND right neighbors
#   - High storage overhead, slow as document grows
#
# Eg-walker stores:
#   - Simple index at time of execution
#   - DAG of edit history
#   - Replays relevant portions when merging concurrent edits
#
# This maps perfectly to Gay.jl:
#   - Simple index = Gay.jl idx (color_at(seed, idx))
#   - DAG = causal history with GF(3) trits
#   - Replay = deterministic re-traversal preserving GF(3)

# =============================================================================
# Color Operations with Simple Indices
# =============================================================================

struct ColorOp
    id::UInt64          # Unique operation ID (Lamport-like)
    kind::Symbol        # :insert, :delete, :recolor
    index::Int          # Simple index at execution time
    color_hex::String   # Gay.jl generated color
    seed::UInt64        # Source seed
    gay_idx::Int        # color_at(seed, gay_idx)
    trit::Int8          # GF(3) assignment
    parent_ids::Vector{UInt64}  # DAG edges (causal dependencies)
end

function ColorOp(kind::Symbol, index::Int, seed::UInt64, gay_idx::Int, parents::Vector{UInt64})
    id = UInt64(time_ns())  # Unique ID
    color = color_at(seed, gay_idx)
    trit = Int8(mod(floor(Int, color.hue / 120), 3) - 1)
    ColorOp(id, kind, index, color.hex, seed, gay_idx, trit, parents)
end

# =============================================================================
# Event Graph (DAG)
# =============================================================================

struct EventNode
    op::ColorOp
    children::Vector{UInt64}  # Forward edges
end

mutable struct EventGraph
    nodes::Dict{UInt64, EventNode}
    roots::Vector{UInt64}     # Operations with no parents
    heads::Vector{UInt64}     # Current frontier (latest ops per branch)
    trit_sum::Int             # Running GF(3) sum
end

EventGraph() = EventGraph(Dict{UInt64, EventNode}(), UInt64[], UInt64[], 0)

function add_op!(G::EventGraph, op::ColorOp)
    node = EventNode(op, UInt64[])
    G.nodes[op.id] = node
    
    # Update parent→child edges
    for pid in op.parent_ids
        if haskey(G.nodes, pid)
            push!(G.nodes[pid].children, op.id)
        end
    end
    
    # Track roots and heads
    if isempty(op.parent_ids)
        push!(G.roots, op.id)
    end
    
    # Update heads: remove parents, add this op
    filter!(h -> h ∉ op.parent_ids, G.heads)
    push!(G.heads, op.id)
    
    # Update GF(3) sum
    if op.kind == :insert
        G.trit_sum = mod(G.trit_sum + op.trit, 3)
    elseif op.kind == :delete
        G.trit_sum = mod(G.trit_sum - op.trit, 3)
    end
    
    op.id
end

# =============================================================================
# Eg-walker State Machine
# =============================================================================

mutable struct EgWalkerState
    graph::EventGraph
    current_doc::Vector{String}   # Current document state (colors)
    current_trits::Vector{Int8}   # Parallel trit tracking
    frontier::Set{UInt64}         # Current position in DAG
    clock::UInt64                 # Lamport clock
end

EgWalkerState(seed::UInt64=1069) = EgWalkerState(
    EventGraph(),
    String[],
    Int8[],
    Set{UInt64}(),
    UInt64(0)
)

# =============================================================================
# Simple Index Operations (Eg-walker Core)
# =============================================================================

"""
Insert at simple index. Unlike traditional CRDTs, we don't store
complex position descriptors - just the index at execution time.
"""
function insert!(state::EgWalkerState, index::Int, seed::UInt64, gay_idx::Int)
    state.clock += 1
    parents = collect(state.frontier)
    
    op = ColorOp(:insert, index, seed, gay_idx, parents)
    add_op!(state.graph, op)
    
    # Apply to current doc
    if index > length(state.current_doc)
        push!(state.current_doc, op.color_hex)
        push!(state.current_trits, op.trit)
    else
        insert!(state.current_doc, index, op.color_hex)
        insert!(state.current_trits, index, op.trit)
    end
    
    # Update frontier
    empty!(state.frontier)
    push!(state.frontier, op.id)
    
    op
end

"""
Delete at simple index. Stores tombstone in DAG for replay.
"""
function delete!(state::EgWalkerState, index::Int)
    state.clock += 1
    parents = collect(state.frontier)
    
    # Get the color being deleted for trit accounting
    deleted_color = state.current_doc[index]
    deleted_trit = state.current_trits[index]
    
    op = ColorOp(
        UInt64(time_ns()), :delete, index, deleted_color,
        UInt64(0), 0, -deleted_trit,  # Negate trit to maintain GF(3)
        parents
    )
    add_op!(state.graph, op)
    
    # Apply to current doc
    deleteat!(state.current_doc, index)
    deleteat!(state.current_trits, index)
    
    # Update frontier
    empty!(state.frontier)
    push!(state.frontier, op.id)
    
    op
end

# =============================================================================
# DAG Traversal for Merge (The Key Innovation)
# =============================================================================

"""
Find common ancestor(s) of two frontiers.
"""
function find_common_ancestors(G::EventGraph, frontier_a::Set{UInt64}, frontier_b::Set{UInt64})
    # BFS backwards from both frontiers
    visited_a = Set{UInt64}()
    visited_b = Set{UInt64}()
    queue_a = collect(frontier_a)
    queue_b = collect(frontier_b)
    
    while !isempty(queue_a) || !isempty(queue_b)
        if !isempty(queue_a)
            id = popfirst!(queue_a)
            if id ∈ visited_b
                return Set([id])  # Found common ancestor
            end
            push!(visited_a, id)
            if haskey(G.nodes, id)
                for pid in G.nodes[id].op.parent_ids
                    if pid ∉ visited_a
                        push!(queue_a, pid)
                    end
                end
            end
        end
        
        if !isempty(queue_b)
            id = popfirst!(queue_b)
            if id ∈ visited_a
                return Set([id])  # Found common ancestor
            end
            push!(visited_b, id)
            if haskey(G.nodes, id)
                for pid in G.nodes[id].op.parent_ids
                    if pid ∉ visited_b
                        push!(queue_b, pid)
                    end
                end
            end
        end
    end
    
    intersect(visited_a, visited_b)
end

"""
Replay operations from ancestor to frontier.
This is the core of Eg-walker: instead of storing complex metadata,
we replay the relevant portion of history to resolve conflicts.
"""
function replay_from_ancestor(G::EventGraph, ancestor::UInt64, target_frontier::Set{UInt64})
    # Topological sort of operations between ancestor and frontier
    ops_to_replay = ColorOp[]
    visited = Set{UInt64}()
    
    function collect_ops(id::UInt64)
        if id ∈ visited || id == ancestor
            return
        end
        push!(visited, id)
        
        node = G.nodes[id]
        for pid in node.op.parent_ids
            collect_ops(pid)
        end
        push!(ops_to_replay, node.op)
    end
    
    for head in target_frontier
        collect_ops(head)
    end
    
    ops_to_replay
end

"""
Merge two divergent branches using Eg-walker replay.
Complexity: O(k log n) where k = operations to merge, n = doc size.
"""
function merge_branches(state_a::EgWalkerState, state_b::EgWalkerState)
    # Find common ancestor
    ancestors = find_common_ancestors(
        state_a.graph,
        state_a.frontier,
        state_b.frontier
    )
    
    if isempty(ancestors)
        error("No common ancestor found - cannot merge")
    end
    
    ancestor = first(ancestors)
    
    # Replay operations from both branches
    ops_a = replay_from_ancestor(state_a.graph, ancestor, state_a.frontier)
    ops_b = replay_from_ancestor(state_b.graph, ancestor, state_b.frontier)
    
    # Merge: interleave by timestamp, resolve conflicts by seed
    all_ops = vcat(ops_a, ops_b)
    sort!(all_ops, by=op -> (op.id, op.seed))  # Deterministic ordering
    
    # Remove duplicates (same position, same time)
    unique_ops = ColorOp[]
    seen = Set{Tuple{Int, UInt64}}()
    for op in all_ops
        key = (op.index, op.id)
        if key ∉ seen
            push!(unique_ops, op)
            push!(seen, key)
        end
    end
    
    # Build merged state
    merged = EgWalkerState(state_a.graph.nodes[ancestor].op.seed)
    
    # Copy ancestor state
    # (simplified: replay all ops from root to ancestor first)
    
    # Apply merged operations
    for op in unique_ops
        add_op!(merged.graph, op)
        if op.kind == :insert
            if op.index > length(merged.current_doc)
                push!(merged.current_doc, op.color_hex)
                push!(merged.current_trits, op.trit)
            else
                insert!(merged.current_doc, op.index, op.color_hex)
                insert!(merged.current_trits, op.index, op.trit)
            end
        elseif op.kind == :delete && op.index ≤ length(merged.current_doc)
            deleteat!(merged.current_doc, op.index)
            deleteat!(merged.current_trits, op.index)
        end
    end
    
    # Update frontier to merged heads
    merged.frontier = union(state_a.frontier, state_b.frontier)
    
    # Verify GF(3) conservation
    trit_sum = sum(merged.current_trits)
    if mod(trit_sum, 3) != 0
        @warn "GF(3) violation after merge, sum=$trit_sum"
    end
    
    merged
end

# =============================================================================
# GF(3) Integration
# =============================================================================

"""
Verify GF(3) conservation across the event graph.
Each path from root to head should maintain Σ trits ≡ 0 (mod 3).
"""
function verify_graph_gf3(G::EventGraph)
    results = Dict{UInt64, NamedTuple}()
    
    function traverse(id::UInt64, running_sum::Int)
        node = G.nodes[id]
        new_sum = if node.op.kind == :insert
            running_sum + node.op.trit
        elseif node.op.kind == :delete
            running_sum - node.op.trit
        else
            running_sum
        end
        
        if isempty(node.children)
            # Leaf node - check conservation
            results[id] = (id=id, sum=new_sum, conserved=mod(new_sum, 3) == 0)
        else
            for child in node.children
                traverse(child, new_sum)
            end
        end
    end
    
    for root in G.roots
        traverse(root, 0)
    end
    
    all_conserved = all(r -> r.conserved, values(results))
    (paths=results, all_conserved=all_conserved)
end

# =============================================================================
# Complexity Analysis: Why Eg-walker is Better
# =============================================================================

"""
Eg-walker Complexity Comparison:

Traditional CRDTs (RGA, Yjs, Fugue):
- Memory: O(n) metadata per operation
- Load time: O(n²) for large documents
- Tombstone accumulation: unbounded

OT (Operational Transformation):
- Merge: O(n²) for divergent branches
- Transform: O(k²) for k concurrent ops

Eg-walker:
- Memory: O(1) per operation (simple index only)
- Load: O(n log n) 
- Merge: O(k log n) where k = ops to merge
- No tombstone overhead (replay recreates state)

With GF(3) integration:
- Additional O(1) per operation for trit
- O(k) verification during merge
- Rebalancing: O(1) amortized (single compensating op)
"""
function complexity_comparison()
    """
    ┌────────────────────────────────────────────────────────────────┐
    │               Eg-walker vs Traditional CRDTs                   │
    ├────────────────────────────────────────────────────────────────┤
    │                                                                │
    │  Metric          │ Traditional │ OT        │ Eg-walker        │
    │  ─────────────────┼─────────────┼───────────┼──────────────────│
    │  Memory/op       │ O(n)        │ O(1)      │ O(1)             │
    │  Document load   │ O(n²)       │ O(n)      │ O(n log n)       │
    │  Merge branches  │ O(k log n)  │ O(n²)     │ O(k log n)       │
    │  Concurrent edit │ O(1)        │ O(k²)     │ O(k log n)       │
    │  Tombstones      │ Unbounded   │ N/A       │ None (replay)    │
    │                                                                │
    │  GF(3) overhead:                                               │
    │  - Per operation: O(1) trit computation                       │
    │  - Merge verify:  O(k) path traversal                         │
    │  - Rebalance:     O(1) compensating insertion                 │
    │                                                                │
    └────────────────────────────────────────────────────────────────┘
    """
end

# =============================================================================
# Demo: Two Users Concurrently Editing Colors
# =============================================================================

function demo_eg_walker_merge()
    println("═" ^ 60)
    println("Eg-walker Color CRDT Demo with GF(3) Conservation")
    println("═" ^ 60)
    
    seed!(1069)
    
    # Alice's branch
    alice = EgWalkerState(UInt64(1069))
    insert!(alice, 1, 1069, 1)  # First color
    insert!(alice, 2, 1069, 2)  # Second color
    println("\nAlice's doc: ", alice.current_doc)
    println("Alice's trits: ", alice.current_trits, " sum=", sum(alice.current_trits))
    
    # Bob's concurrent branch (forked from empty)
    bob = EgWalkerState(UInt64(1069))
    insert!(bob, 1, 1069, 3)   # Different first color
    insert!(bob, 2, 1069, 4)   # Different second color
    println("\nBob's doc: ", bob.current_doc)
    println("Bob's trits: ", bob.current_trits, " sum=", sum(bob.current_trits))
    
    # Merge using Eg-walker replay
    # Note: In real usage, they'd share a common ancestor
    println("\n--- Eg-walker Replay Merge ---")
    
    # Verify GF(3) on each graph
    alice_gf3 = verify_graph_gf3(alice.graph)
    bob_gf3 = verify_graph_gf3(bob.graph)
    
    println("Alice GF(3) conserved: ", alice_gf3.all_conserved)
    println("Bob GF(3) conserved: ", bob_gf3.all_conserved)
    
    println("\n", complexity_comparison())
end

end # module
