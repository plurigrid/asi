"""
    NavigationCaching

Efficient proof navigation with intelligent caching and non-backtracking constraints.

Phase 2 Stage 3: Navigation Caching Implementation
=================================================

This module implements O(1) proof lookup by caching comprehension regions
in a bidirectional index structure, with constraints from Friedman's
non-backtracking operator to prevent wasteful search paths.

Key Features:
- O(1) proof lookup via cached bidirectional index
- Non-backtracking constraint enforcement
- Comprehension region integration
- LHoTT resource tracking
- Health-aware caching strategy
"""

module NavigationCaching

using LinearAlgebra
using Statistics
using Dates

# Export public API
export
    ProofCache,
    CacheEntry,
    NavigationSession,
    initialize_proof_cache,
    lookup_proof,
    cache_comprehension_region,
    find_cached_proofs,
    get_cache_statistics,
    start_navigation_session,
    update_navigation_context

# ============================================================================
# Part 1: Data Structures
# ============================================================================

"""
    CacheEntry

A single cached proof path with metadata.
"""
mutable struct CacheEntry
    theorem_id::Int
    proof_path::Vector{Int}                    # Path to proof
    comprehension_region::Int                  # Which region this proof belongs to
    access_count::Int                          # How many times accessed
    last_accessed::Float64                     # Last access timestamp
    resource_cost::Float64                     # LHoTT resource consumption
    success_rate::Float64                      # % of attempts that succeeded
end

"""
    ProofCache

Bidirectional index for O(1) proof lookup with caching.
"""
mutable struct ProofCache
    entries::Dict{Int, CacheEntry}             # theorem_id → CacheEntry
    region_to_theorems::Dict{Int, Vector{Int}} # region_id → [theorem_ids]
    forward_index::Dict{Int, Vector{Int}}      # From theorem → To theorems
    reverse_index::Dict{Int, Vector{Int}}      # To theorem → From theorems
    cache_hits::Int
    cache_misses::Int
    total_lookups::Int
    last_updated::Float64
end

"""
    NavigationSession

State tracking for a proof navigation session.
"""
mutable struct NavigationSession
    session_id::String
    theorem_id::Int
    cache::ProofCache
    visited_theorems::Set{Int}                 # Prevent backtracking
    path_history::Vector{Vector{Int}}          # Full path history
    current_path::Vector{Int}                  # Current path
    resource_budget::Float64                   # LHoTT resource budget
    resource_used::Float64                     # Resources consumed
    health_gap::Float64                        # System health at session start
    timestamp::Float64
end

# ============================================================================
# Part 2: Cache Initialization
# ============================================================================

"""
    initialize_proof_cache() -> ProofCache

Create an empty proof cache structure.
"""
function initialize_proof_cache()::ProofCache
    return ProofCache(
        Dict{Int, CacheEntry}(),
        Dict{Int, Vector{Int}}(),
        Dict{Int, Vector{Int}}(),
        Dict{Int, Vector{Int}}(),
        0,
        0,
        0,
        time()
    )
end

"""
    cache_comprehension_region(cache::ProofCache, region_id::Int,
                               theorems::Vector{Int},
                               adjacency::Matrix) -> ProofCache

Load comprehension region into proof cache.
Constructs bidirectional index from adjacency matrix.
"""
function cache_comprehension_region(
    cache::ProofCache,
    region_id::Int,
    theorems::Vector{Int},
    adjacency::Matrix
)::ProofCache

    # Store region membership
    cache.region_to_theorems[region_id] = theorems

    # Build forward and reverse indices from adjacency matrix
    for theorem in theorems
        # Forward index: theorem → all theorems it connects to
        connections = Int[]
        if theorem <= size(adjacency, 1)
            for (idx, score) in enumerate(adjacency[theorem, :])
                if score > 0.5 && idx in theorems && idx != theorem
                    push!(connections, idx)
                end
            end
        end
        cache.forward_index[theorem] = connections

        # Reverse index: theorem ← all theorems that connect to it
        reverse_connections = Int[]
        if theorem <= size(adjacency, 2)
            for (idx, score) in enumerate(adjacency[:, theorem])
                if score > 0.5 && idx in theorems && idx != theorem
                    push!(reverse_connections, idx)
                end
            end
        end
        cache.reverse_index[theorem] = reverse_connections

        # Create cache entry
        cache.entries[theorem] = CacheEntry(
            theorem,
            Int[],                    # Empty path initially
            region_id,
            0,                        # No accesses yet
            time(),
            0.0,                      # No resource cost yet
            0.0                       # No success rate yet
        )
    end

    cache.last_updated = time()
    return cache
end

# ============================================================================
# Part 3: Proof Lookup (O(1) via cache)
# ============================================================================

"""
    lookup_proof(theorem_id::Int, cache::ProofCache) -> Union{Vector{Int}, Nothing}

O(1) lookup of cached proof for theorem.
Returns proof path or nothing if not cached.
"""
function lookup_proof(theorem_id::Int, cache::ProofCache)::Union{Vector{Int}, Nothing}
    cache.total_lookups += 1

    if haskey(cache.entries, theorem_id)
        entry = cache.entries[theorem_id]
        cache.cache_hits += 1
        entry.access_count += 1
        entry.last_accessed = time()
        return entry.proof_path
    else
        cache.cache_misses += 1
        return nothing
    end
end

"""
    find_cached_proofs(theorem_id::Int, cache::ProofCache,
                      max_depth::Int=2) -> Vector{Vector{Int}}

Find all proofs within max_depth hops using cached bidirectional index.
"""
function find_cached_proofs(
    theorem_id::Int,
    cache::ProofCache,
    max_depth::Int=2
)::Vector{Vector{Int}}

    proofs = Vector{Vector{Int}}()

    # BFS with bidirectional constraint (prevent u->v->u cycles)
    visited = Set{Int}([theorem_id])

    # Use separate arrays for queue components to avoid type issues
    queue_current = Int[theorem_id]
    queue_depth = Int[0]
    queue_paths = Vector{Vector{Int}}([Int[theorem_id]])

    while !isempty(queue_current)
        current = popfirst!(queue_current)
        depth = popfirst!(queue_depth)
        path = popfirst!(queue_paths)

        if depth > 0 && current != theorem_id
            push!(proofs, path)
        end

        if depth < max_depth
            # Forward connections (non-backtracking)
            if haskey(cache.forward_index, current)
                for next_theorem in cache.forward_index[current]
                    # Non-backtracking constraint: can't revisit
                    if next_theorem ∉ visited
                        push!(visited, next_theorem)
                        new_path = vcat(path, [next_theorem])
                        push!(queue_current, next_theorem)
                        push!(queue_depth, depth + 1)
                        push!(queue_paths, new_path)
                    end
                end
            end
        end
    end

    return proofs
end

# ============================================================================
# Part 4: Navigation Sessions
# ============================================================================

"""
    start_navigation_session(theorem_id::Int, cache::ProofCache,
                            health_gap::Float64, resource_budget::Float64)
        -> NavigationSession

Start a new proof navigation session.
"""
function start_navigation_session(
    theorem_id::Int,
    cache::ProofCache,
    health_gap::Float64,
    resource_budget::Float64=1000.0
)::NavigationSession

    return NavigationSession(
        "nav_$(theorem_id)_$(floor(Int, time()*1000))",
        theorem_id,
        cache,
        Set{Int}([theorem_id]),
        Vector{Vector{Int}}[],
        Int[theorem_id],
        resource_budget,
        0.0,
        health_gap,
        time()
    )
end

"""
    update_navigation_context(session::NavigationSession, next_theorem::Int,
                             resource_cost::Float64)
        -> Bool

Update session context with next theorem in path.
Returns true if valid (respects constraints), false if invalid.
"""
function update_navigation_context(
    session::NavigationSession,
    next_theorem::Int,
    resource_cost::Float64=10.0
)::Bool

    # Check non-backtracking constraint
    if next_theorem in session.visited_theorems
        return false  # Can't revisit (non-backtracking)
    end

    # Check resource budget
    if session.resource_used + resource_cost > session.resource_budget
        return false  # Insufficient resources
    end

    # Update session state
    push!(session.visited_theorems, next_theorem)
    push!(session.current_path, next_theorem)
    session.resource_used += resource_cost

    return true
end

# ============================================================================
# Part 5: Cache Statistics
# ============================================================================

"""
    get_cache_statistics(cache::ProofCache) -> Dict

Get comprehensive cache statistics.
"""
function get_cache_statistics(cache::ProofCache)::Dict
    total_lookups = max(cache.total_lookups, 1)  # Avoid division by zero
    hit_rate = cache.cache_hits / total_lookups * 100

    # Compute average access counts
    if !isempty(cache.entries)
        access_counts = [entry.access_count for entry in values(cache.entries)]
        avg_accesses = mean(access_counts)
        max_accesses = maximum(access_counts)
    else
        avg_accesses = 0.0
        max_accesses = 0
    end

    # Compute region sizes
    region_sizes = [length(theorems) for theorems in values(cache.region_to_theorems)]
    avg_region_size = if !isempty(region_sizes)
        mean(region_sizes)
    else
        0.0
    end

    return Dict(
        :total_cached => length(cache.entries),
        :total_regions => length(cache.region_to_theorems),
        :total_lookups => cache.total_lookups,
        :cache_hits => cache.cache_hits,
        :cache_misses => cache.cache_misses,
        :hit_rate => hit_rate,
        :avg_access_count => avg_accesses,
        :max_access_count => max_accesses,
        :avg_region_size => avg_region_size,
        :last_updated => cache.last_updated
    )
end

# ============================================================================
# Part 6: Health-Aware Caching Strategy
# ============================================================================

"""
    compute_cache_priority(entry::CacheEntry, current_health::Float64)
        -> Float64

Compute priority score for cache entry based on health.
Higher score = higher priority for keeping in cache.
"""
function compute_cache_priority(entry::CacheEntry, current_health::Float64)::Float64
    # Weight factors
    access_weight = 0.4
    success_weight = 0.3
    recency_weight = 0.2
    health_weight = 0.1

    # Normalize access count (log scale)
    access_score = log(max(entry.access_count + 1, 1.0)) / 10.0

    # Success rate directly
    success_score = entry.success_rate

    # Recency (decay over hours)
    hours_ago = (time() - entry.last_accessed) / 3600
    recency_score = exp(-hours_ago / 24)  # Decay over 24 hours

    # Health adjustment
    health_score = current_health >= 0.25 ? 1.0 : 0.5

    return (access_weight * access_score +
            success_weight * success_score +
            recency_weight * recency_score +
            health_weight * health_score)
end

"""
    evict_low_priority_entries(cache::ProofCache, health_gap::Float64,
                              target_size::Int=100)

Remove lowest-priority entries when cache exceeds target size.
"""
function evict_low_priority_entries(
    cache::ProofCache,
    health_gap::Float64,
    target_size::Int=100
)

    if length(cache.entries) <= target_size
        return  # No eviction needed
    end

    # Compute priorities for all entries
    priorities = Dict{Int, Float64}()
    for (theorem_id, entry) in cache.entries
        priorities[theorem_id] = compute_cache_priority(entry, health_gap)
    end

    # Sort by priority (ascending)
    sorted = sort(collect(priorities), by=x -> x[2])

    # Evict lowest priority entries
    num_to_evict = length(cache.entries) - target_size
    for i in 1:num_to_evict
        theorem_id = sorted[i][1]
        delete!(cache.entries, theorem_id)
    end
end

end  # module NavigationCaching
