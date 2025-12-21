#!/usr/bin/env julia
# crdt_memoization/core.jl
#
# CRDT Core Data Structures with Content-Addressed Memoization
#
# Implements 6 CRDT types (TextCRDT, JSONCRDT, GCounter, PNCounter, ORSet, TAPStateCRDT)
# Each with:
# - Fingerprint field (FNV-1a content hash) for content-addressed caching
# - Vector clock tracking for causality
# - Join-semilattice interface (S, ⊔) where merge is commutative/associative/idempotent
#
# Extends colored_sexp_acset.jl GadgetCache pattern for memoization:
# - Polarity-indexed cache (positive/negative/neutral)
# - Staleness detection via vector clock comparison
# - Lazy evaluation queue for parallel processing
#

using Dates

# =============================================================================
# Vector Clock (Causality Tracking)
# =============================================================================

"""
VectorClock tracks causality across distributed agents.
Implements Lamport-style logical timestamps for each agent.
"""
mutable struct VectorClock
    clocks::Dict{String, UInt64}  # agent_id → logical clock
    timestamp::DateTime            # Physical timestamp for reference
end

VectorClock() = VectorClock(Dict{String, UInt64}(), now())

function increment!(vc::VectorClock, agent_id::String)::UInt64
    vc.clocks[agent_id] = get(vc.clocks, agent_id, 0) + 1
    vc.clocks[agent_id]
end

function merge_clocks(vc1::VectorClock, vc2::VectorClock)::VectorClock
    merged = Dict{String, UInt64}()
    for (agent_id, clock) in vc1.clocks
        merged[agent_id] = clock
    end
    for (agent_id, clock) in vc2.clocks
        merged[agent_id] = max(get(merged, agent_id, 0), clock)
    end
    VectorClock(merged, now())
end

function is_causally_after(vc1::VectorClock, vc2::VectorClock)::Bool
    # vc1 causally dominates vc2 if all clocks ≥ and at least one strictly greater
    greater_found = false
    for (agent_id, clock1) in vc1.clocks
        clock2 = get(vc2.clocks, agent_id, 0)
        clock1 < clock2 && return false  # vc1 is behind on this agent
        clock1 > clock2 && (greater_found = true)
    end
    greater_found
end

# Hash for vector clock (for cache keys)
function Base.hash(vc::VectorClock, h::UInt64 = 0x9e3779b97f4a7c15)
    for (agent_id, clock) in sort(collect(vc.clocks))
        h = hash((agent_id, clock), h)
    end
    h
end

# =============================================================================
# FNV-1a Fingerprinting (Content-Addressed Hashing)
# =============================================================================

const FNV_PRIME = 0x100000001b3
const FNV_OFFSET = 0xcbf29ce484222325

"""
FNV-1a content hash for deterministic fingerprinting.
Essential for content-addressed merge caching.
"""
function fnv1a_hash(data::Union{String, Vector, Tuple})::UInt64
    hash = FNV_OFFSET
    if data isa String
        for byte in codeunits(data)
            hash = hash ⊻ UInt64(byte)
            hash = (hash * FNV_PRIME) & 0xffffffffffffffff
        end
    else
        for item in data
            hash = hash ⊻ hash(item)
            hash = (hash * FNV_PRIME) & 0xffffffffffffffff
        end
    end
    hash
end

# =============================================================================
# 1. Text CRDT (Fractional Indexing with Tombstones)
# =============================================================================

"""
TextCRDT: Conflict-free text with fractional indices and tombstones
Inspired by crdt.el pattern from Derrick Stolee.

Operations:
- insert(pos, chars) → (fraction_index, chars, agent_id)
- delete(pos) → creates tombstone entry

Join operation merges based on fractional position ordering.
"""
mutable struct TextCRDT
    # Content: map of (fractional_index, agent_id) → character
    content::Dict{Tuple{Float64, String}, Char}

    # Tombstones: set of deleted positions
    tombstones::Set{Tuple{Float64, String}}

    # Causality
    vector_clock::VectorClock

    # Content address (FNV-1a hash)
    fingerprint::UInt64

    # Metadata
    agent_id::String
    created_at::DateTime
end

function TextCRDT(agent_id::String)
    vc = VectorClock()
    TextCRDT(
        Dict{Tuple{Float64, String}, Char}(),
        Set{Tuple{Float64, String}}(),
        vc,
        fnv1a_hash(""),
        agent_id,
        now()
    )
end

function insert_char!(crdt::TextCRDT, pos::Int, char::Char)
    # Generate fractional index
    idx = Float64(pos) + (rand() / 10000.0)
    key = (idx, crdt.agent_id)

    crdt.content[key] = char
    delete!(crdt.tombstones, key)

    # Update causality
    increment!(crdt.vector_clock, crdt.agent_id)

    # Recompute fingerprint
    sorted_keys = sort(collect(keys(crdt.content)), by=x -> x[1])
    content_str = join([crdt.content[k] for k in sorted_keys])
    crdt.fingerprint = fnv1a_hash(content_str)
end

function delete_char!(crdt::TextCRDT, pos::Int)
    # Get key at position
    sorted_keys = sort(collect(keys(crdt.content)), by=x -> x[1])
    if pos > 0 && pos <= length(sorted_keys)
        key = sorted_keys[pos]
        delete!(crdt.content, key)
        push!(crdt.tombstones, key)

        increment!(crdt.vector_clock, crdt.agent_id)
        remaining_keys = sort(collect(keys(crdt.content)), by=x -> x[1])
        content_str = join([crdt.content[k] for k in remaining_keys])
        crdt.fingerprint = fnv1a_hash(content_str)
    end
end

function Base.String(crdt::TextCRDT)::String
    # Sort keys by fractional index to ensure consistent ordering
    sorted_keys = sort(collect(keys(crdt.content)), by=x -> x[1])
    join([crdt.content[k] for k in sorted_keys])
end

# =============================================================================
# 2. JSON CRDT (Last-Write-Wins Nested Documents)
# =============================================================================

"""
JSONCRDT: Conflict-free JSON with Last-Write-Wins resolution
Plurigrid bft-json-crdt style with timestamp-based conflict resolution.

Structure: Nested maps with (value, timestamp, agent_id) at leaf level
Join operation: Select entry with highest timestamp (tiebreak by agent_id)
"""
mutable struct JSONCRDT
    # Nested dict: path (Vector of keys) → (value, timestamp, agent_id)
    data::Dict{Vector{String}, Tuple{Any, DateTime, String}}

    # Causality
    vector_clock::VectorClock

    # Content address
    fingerprint::UInt64

    # Metadata
    agent_id::String
    created_at::DateTime
end

function JSONCRDT(agent_id::String)
    vc = VectorClock()
    JSONCRDT(
        Dict{Vector{String}, Tuple{Any, DateTime, String}}(),
        vc,
        fnv1a_hash("{}"),
        agent_id,
        now()
    )
end

function set_value!(crdt::JSONCRDT, path::Vector{String}, value::Any)
    crdt.data[path] = (value, now(), crdt.agent_id)
    increment!(crdt.vector_clock, crdt.agent_id)

    # Recompute fingerprint from sorted structure
    items = sort(collect(crdt.data), by=first)
    crdt.fingerprint = fnv1a_hash(string(items))
end

function get_value(crdt::JSONCRDT, path::Vector{String})
    get(crdt.data, path, (nothing, nothing, nothing))[1]
end

# =============================================================================
# 3. Counter CRDTs (G-Counter and PN-Counter)
# =============================================================================

"""
GCounter: Grow-only counter (increment only)
Each agent maintains separate counter, join is per-agent maximum.
"""
mutable struct GCounter
    # agent_id → current count
    increments::Dict{String, UInt64}

    # Causality
    vector_clock::VectorClock
    fingerprint::UInt64
    agent_id::String
    created_at::DateTime
end

function GCounter(agent_id::String)
    GCounter(
        Dict{String, UInt64}(),
        VectorClock(),
        fnv1a_hash("0"),
        agent_id,
        now()
    )
end

function increment!(counter::GCounter, amount::Union{Int, UInt64} = 1)
    counter.increments[counter.agent_id] =
        get(counter.increments, counter.agent_id, 0) + UInt64(amount)
    increment!(counter.vector_clock, counter.agent_id)
    counter.fingerprint = fnv1a_hash(string(sort(collect(counter.increments))))
end

function value(counter::GCounter)::UInt64
    sum(values(counter.increments); init=0)
end

"""
PNCounter: Positive-Negative counter (increment and decrement)
Two separate GCounters (positive and negative).
"""
mutable struct PNCounter
    positive::GCounter
    negative::GCounter
    vector_clock::VectorClock
    fingerprint::UInt64
    agent_id::String
    created_at::DateTime
end

function PNCounter(agent_id::String)
    PNCounter(
        GCounter(agent_id),
        GCounter(agent_id),
        VectorClock(),
        fnv1a_hash("0"),
        agent_id,
        now()
    )
end

function increment!(counter::PNCounter, amount::Union{Int, UInt64} = 1)
    increment!(counter.positive, amount)
    merge_clocks(counter.positive.vector_clock, counter.negative.vector_clock)
    counter.fingerprint = fnv1a_hash(string((value(counter.positive), value(counter.negative))))
end

function decrement!(counter::PNCounter, amount::Union{Int, UInt64} = 1)
    increment!(counter.negative, amount)
    merge_clocks(counter.positive.vector_clock, counter.negative.vector_clock)
    counter.fingerprint = fnv1a_hash(string((value(counter.positive), value(counter.negative))))
end

function value(counter::PNCounter)::Int64
    Int64(value(counter.positive)) - Int64(value(counter.negative))
end

# =============================================================================
# 4. OR-Set (Observed-Remove Set)
# =============================================================================

"""
ORSet: Conflict-free set with add/remove via unique tags.
Each element tagged with (element, agent_id, timestamp).
Remove needs to know specific tag to prevent resurrection.
"""
mutable struct ORSet
    # element → Set of (agent_id, timestamp) tags
    elements::Dict{Any, Set{Tuple{String, UInt64}}}

    # Tombstones: explicitly tracked removals
    tombstones::Set{Tuple{Any, String, UInt64}}

    # Causality
    vector_clock::VectorClock
    fingerprint::UInt64
    agent_id::String
    created_at::DateTime
end

function ORSet(agent_id::String)
    ORSet(
        Dict{Any, Set{Tuple{String, UInt64}}}(),
        Set{Tuple{Any, String, UInt64}}(),
        VectorClock(),
        fnv1a_hash("{}"),
        agent_id,
        now()
    )
end

function add!(set::ORSet, element::Any)
    timestamp = increment!(set.vector_clock, set.agent_id)
    tag = (set.agent_id, timestamp)

    if !haskey(set.elements, element)
        set.elements[element] = Set{Tuple{String, UInt64}}()
    end
    push!(set.elements[element], tag)

    # Update fingerprint
    set.fingerprint = fnv1a_hash(string(sort(collect(keys(set.elements)))))
end

function remove!(set::ORSet, element::Any)
    if haskey(set.elements, element)
        for tag in set.elements[element]
            push!(set.tombstones, (element, tag[1], tag[2]))
        end
        delete!(set.elements, element)
        set.fingerprint = fnv1a_hash(string(sort(collect(keys(set.elements)))))
    end
end

function contains(set::ORSet, element::Any)::Bool
    haskey(set.elements, element) && !isempty(set.elements[element])
end

function members(set::ORSet)::Set{Any}
    Set(k for k in keys(set.elements) if !isempty(set.elements[k]))
end

# =============================================================================
# 5. TAP State CRDT (Balanced Ternary -1/0/+1)
# =============================================================================

"""
TAPStateCRDT: Balanced ternary state tracking (from colored_sexp_acset.jl pattern)
States: -1 (Backfill), 0 (Verify), +1 (Live)

Used for distributed control flow in music-topos system.
"""
@enum TAPState::Int8 begin
    BACKFILL = -1
    VERIFY = 0
    LIVE = 1
end

mutable struct TAPStateCRDT
    # Current state (highest state wins in merge)
    state::TAPState

    # History of state transitions (for causality)
    history::Vector{Tuple{TAPState, DateTime, String}}

    # Causality
    vector_clock::VectorClock
    fingerprint::UInt64
    agent_id::String
    created_at::DateTime
end

function TAPStateCRDT(agent_id::String, initial_state::TAPState = LIVE)
    vc = VectorClock()
    increment!(vc, agent_id)
    crdt = TAPStateCRDT(
        initial_state,
        Vector{Tuple{TAPState, DateTime, String}}(),
        vc,
        fnv1a_hash(string(Int8(initial_state))),
        agent_id,
        now()
    )
    push!(crdt.history, (initial_state, now(), agent_id))
    crdt
end

function transition_state!(crdt::TAPStateCRDT, new_state::TAPState)
    if new_state != crdt.state
        crdt.state = new_state
        push!(crdt.history, (new_state, now(), crdt.agent_id))
        increment!(crdt.vector_clock, crdt.agent_id)
        crdt.fingerprint = fnv1a_hash(string(Int8(new_state)))
    end
end

# =============================================================================
# Join-Semilattice Protocol (Abstract Interface)
# =============================================================================

"""
All CRDT types implement join-semilattice: (S, ⊔)
where:
  - S = set of all states
  - ⊔ = merge operation

Properties:
  1. Commutativity: merge(a, b) = merge(b, a)
  2. Associativity: merge(merge(a, b), c) = merge(a, merge(b, c))
  3. Idempotence: merge(a, a) = a
"""

function merge(crdt1::TextCRDT, crdt2::TextCRDT)::TextCRDT
    # Merge content: union with fractional indices preserved
    merged = TextCRDT(crdt1.agent_id)
    for (key, char) in crdt1.content
        merged.content[key] = char
    end
    for (key, char) in crdt2.content
        merged.content[key] = char  # Overwrite if present (later agent wins)
    end

    # Merge tombstones (union)
    merged.tombstones = union(crdt1.tombstones, crdt2.tombstones)

    # Clean up deleted chars
    for key in merged.tombstones
        delete!(merged.content, key)
    end

    # Merge vector clocks
    merged.vector_clock = merge_clocks(crdt1.vector_clock, crdt2.vector_clock)

    # Update fingerprint with sorted keys
    sorted_keys = sort(collect(keys(merged.content)), by=x -> x[1])
    content_str = join([merged.content[k] for k in sorted_keys])
    merged.fingerprint = fnv1a_hash(content_str)

    merged
end

function merge(crdt1::GCounter, crdt2::GCounter)::GCounter
    merged = GCounter(crdt1.agent_id)
    for (agent_id, count) in crdt1.increments
        merged.increments[agent_id] = max(
            get(merged.increments, agent_id, 0),
            count
        )
    end
    for (agent_id, count) in crdt2.increments
        merged.increments[agent_id] = max(
            get(merged.increments, agent_id, 0),
            count
        )
    end
    merged.vector_clock = merge_clocks(crdt1.vector_clock, crdt2.vector_clock)
    merged.fingerprint = fnv1a_hash(string(sort(collect(merged.increments))))
    merged
end

function merge(set1::ORSet, set2::ORSet)::ORSet
    merged = ORSet(set1.agent_id)

    # Union all tags from both sets
    for (element, tags) in set1.elements
        if !haskey(merged.elements, element)
            merged.elements[element] = Set{Tuple{String, UInt64}}()
        end
        union!(merged.elements[element], tags)
    end
    for (element, tags) in set2.elements
        if !haskey(merged.elements, element)
            merged.elements[element] = Set{Tuple{String, UInt64}}()
        end
        union!(merged.elements[element], tags)
    end

    # Merge tombstones
    merged.tombstones = union(set1.tombstones, set2.tombstones)

    # Clean up tombstoned elements
    for (element, agent_id, timestamp) in merged.tombstones
        if haskey(merged.elements, element)
            delete!(merged.elements[element], (agent_id, timestamp))
            if isempty(merged.elements[element])
                delete!(merged.elements, element)
            end
        end
    end

    merged.vector_clock = merge_clocks(set1.vector_clock, set2.vector_clock)
    merged.fingerprint = fnv1a_hash(string(sort(collect(keys(merged.elements)))))
    merged
end

function merge(tap1::TAPStateCRDT, tap2::TAPStateCRDT)::TAPStateCRDT
    # Higher state wins (Backfill < Verify < Live)
    merged_state = max(tap1.state, tap2.state)
    merged = TAPStateCRDT(tap1.agent_id, merged_state)

    # Merge history: combine and sort by timestamp
    all_history = vcat(tap1.history, tap2.history)
    sort!(all_history, by=x -> x[2])
    merged.history = all_history

    merged.vector_clock = merge_clocks(tap1.vector_clock, tap2.vector_clock)
    merged.fingerprint = fnv1a_hash(string(Int8(merged_state)))
    merged
end

# =============================================================================
# Exports
# =============================================================================

export TextCRDT, JSONCRDT, GCounter, PNCounter, ORSet, TAPStateCRDT, TAPState
export VectorClock, fnv1a_hash
export merge, insert_char!, delete_char!, increment!, decrement!
export add!, remove!, contains, members, transition_state!
export BACKFILL, VERIFY, LIVE
