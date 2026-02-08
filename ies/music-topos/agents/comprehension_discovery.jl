"""
    ComprehensionDiscovery

Comprehension-guided theorem discovery for agents using spectral random walk regions.
Enables agents to discover related theorems based on co-visitation patterns.

Phase 2 Stage 2: Comprehension-Guided Discovery Implementation
================================================================

This module integrates spectral random walk comprehension discovery with agent
proof attempts, enabling intelligent theorem selection based on proof accessibility.
"""

module ComprehensionDiscovery

using LinearAlgebra
using Statistics
using Random
using Dates

# Import spectral random walk for comprehension discovery
skill_path = if isfile("../.codex/skills/spectral-random-walker/spectral_random_walk.jl")
    "../.codex/skills/spectral-random-walker/spectral_random_walk.jl"
elseif isfile("../../.codex/skills/spectral-random-walker/spectral_random_walk.jl")
    "../../.codex/skills/spectral-random-walker/spectral_random_walk.jl"
else
    "/Users/bob/ies/music-topos/.codex/skills/spectral-random-walker/spectral_random_walk.jl"
end

USE_REAL_WALKER = false
COMPREHENSION_CACHE = nothing

try
    include(skill_path)
    import .SpectralRandomWalk
    USE_REAL_WALKER = true
catch e
    @warn "Could not load SpectralRandomWalk: $e, using fallback simulated regions"
    USE_REAL_WALKER = false
end

export
    ComprehensionRegion,
    DiscoverySession,
    discover_related_theorems,
    get_comprehension_region,
    sample_theorems_by_covisitation,
    initialize_comprehension,
    get_region_statistics

# ============================================================================
# Part 1: Data Structures
# ============================================================================

"""
    ComprehensionRegion

Represents a group of theorems frequently co-visited in random walks.
Theorems in the same region are likely to have related proofs.
"""
mutable struct ComprehensionRegion
    region_id::Int
    theorems::Vector{Int}
    centrality::Dict{Int, Float64}      # Co-visitation centrality scores
    size::Int
    min_covisit::Float64
    max_covisit::Float64
end

"""
    DiscoverySession

Tracks comprehension discovery state for a proof search session.
"""
mutable struct DiscoverySession
    session_id::String
    theorem_id::Int
    region::ComprehensionRegion
    discovered_theorems::Vector{Int}
    covisitation_scores::Vector{Float64}
    timestamp::Float64
    health_gap::Float64
end

# ============================================================================
# Part 2: Weighted Sampling Helper
# ============================================================================

"""
Weighted sample from array with probabilities.
"""
function sample_with_weights(items::Vector, weights::Vector, num_samples::Int)::Vector
    if isempty(items)
        return []
    end

    num_samples = min(num_samples, length(items))

    # Normalize weights to probabilities
    total_weight = sum(weights)
    probs = weights ./ total_weight

    # Sample indices based on weights (without replacement)
    sampled_indices = Int[]
    for _ in 1:num_samples
        # Create cumulative distribution
        cumsum_probs = cumsum(probs)

        # Sample index based on probabilities
        rand_val = rand()
        idx = findfirst(cp -> cp >= rand_val, cumsum_probs)
        if idx !== nothing
            push!(sampled_indices, idx)

            # Zero out probability of selected item (for no replacement)
            probs[idx] = 0.0
            total_weight -= weights[idx]
            if total_weight > 0
                probs = probs ./ total_weight
            end
        end
    end

    return items[unique(sampled_indices)]
end

# ============================================================================
# Part 3: Fallback Comprehension Discovery
# ============================================================================

"""
Generate fallback comprehension regions for testing without real random walk.
Clusters theorems into synthetic regions based on simple heuristics.
"""
function generate_fallback_regions(num_theorems::Int=100, num_regions::Int=5)
    regions = Dict{Int, ComprehensionRegion}()

    theorems_per_region = div(num_theorems, num_regions)

    for region_id in 1:num_regions
        start_idx = (region_id - 1) * theorems_per_region + 1
        end_idx = region_id == num_regions ? num_theorems : region_id * theorems_per_region

        region_theorems = collect(start_idx:end_idx)

        # Simulate co-visitation scores (higher toward region center)
        centrality = Dict{Int, Float64}()
        for (idx, theorem) in enumerate(region_theorems)
            # Score based on distance from region center
            dist_from_center = abs(idx - length(region_theorems)/2) / length(region_theorems)
            centrality[theorem] = 0.8 - 0.5 * dist_from_center + randn() * 0.1
        end

        regions[region_id] = ComprehensionRegion(
            region_id,
            region_theorems,
            centrality,
            length(region_theorems),
            minimum(values(centrality)),
            maximum(values(centrality))
        )
    end

    return regions
end

# ============================================================================
# Part 3: Initialization and Caching
# ============================================================================

"""
    initialize_comprehension(adjacency::Matrix, gap::Float64) -> Dict

Initialize comprehension discovery for a proof system.
Loads real comprehension regions or generates fallback regions.
"""
function initialize_comprehension(adjacency::Matrix, gap::Float64)::Dict
    global COMPREHENSION_CACHE

    try
        if USE_REAL_WALKER && !isnothing(adjacency)
            # Use real comprehension discovery
            comprehension = SpectralRandomWalk.comprehension_discovery(adjacency, gap)

            # Extract regions for easier access
            regions = Dict{Int, ComprehensionRegion}()
            co_visit_matrix = comprehension["co_visit_matrix"]
            region_assignments = comprehension["comprehension_regions"]

            # Convert to region objects
            num_theorems = size(co_visit_matrix, 1)

            # Find unique regions
            unique_regions = unique(values(region_assignments))
            for (region_id, region_theorems) in enumerate(unique_regions)
                if !isempty(region_theorems)
                    # Get co-visitation scores for this region
                    centrality = Dict{Int, Float64}()
                    for theorem in region_theorems
                        scores = co_visit_matrix[theorem, region_theorems]
                        centrality[theorem] = mean(scores)
                    end

                    regions[region_id] = ComprehensionRegion(
                        region_id,
                        region_theorems,
                        centrality,
                        length(region_theorems),
                        minimum(values(centrality)),
                        maximum(values(centrality))
                    )
                end
            end

            COMPREHENSION_CACHE = Dict(
                :regions => regions,
                :co_visit_matrix => co_visit_matrix,
                :timestamp => time(),
                :gap => gap
            )

            return COMPREHENSION_CACHE
        else
            # Fallback: generate synthetic regions
            num_theorems = size(adjacency, 1)
            regions = generate_fallback_regions(num_theorems, max(2, div(num_theorems, 20)))

            # Create synthetic co-visit matrix
            co_visit_matrix = zeros(num_theorems, num_theorems)
            for (region_id, region) in regions
                for (idx1, t1) in enumerate(region.theorems)
                    for (idx2, t2) in enumerate(region.theorems)
                        co_visit_matrix[t1, t2] = region.centrality[t1] * region.centrality[t2]
                    end
                end
            end

            COMPREHENSION_CACHE = Dict(
                :regions => regions,
                :co_visit_matrix => co_visit_matrix,
                :timestamp => time(),
                :gap => gap
            )

            return COMPREHENSION_CACHE
        end
    catch e
        @warn "Comprehension initialization failed: $e, using fallback"

        # Ultimate fallback
        num_theorems = size(adjacency, 1)
        regions = generate_fallback_regions(num_theorems, max(2, div(num_theorems, 20)))
        co_visit_matrix = zeros(num_theorems, num_theorems)

        COMPREHENSION_CACHE = Dict(
            :regions => regions,
            :co_visit_matrix => co_visit_matrix,
            :timestamp => time(),
            :gap => 0.25
        )

        return COMPREHENSION_CACHE
    end
end

# ============================================================================
# Part 4: Theorem Discovery Functions
# ============================================================================

"""
    get_comprehension_region(theorem_id::Int, comprehension::Dict) -> ComprehensionRegion

Get the comprehension region containing a specific theorem.
"""
function get_comprehension_region(theorem_id::Int, comprehension::Dict)::ComprehensionRegion
    for (region_id, region) in comprehension[:regions]
        if theorem_id in region.theorems
            return region
        end
    end

    # Fallback: create empty region
    return ComprehensionRegion(
        -1,
        [theorem_id],
        Dict(theorem_id => 0.0),
        1,
        0.0,
        0.0
    )
end

"""
    discover_related_theorems(theorem_id::Int, comprehension::Dict;
                             num_to_discover::Int=10) -> Vector{Int}

Discover theorems related to the target theorem based on comprehension region.
Returns theorems weighted by co-visitation scores.
"""
function discover_related_theorems(
    theorem_id::Int,
    comprehension::Dict;
    num_to_discover::Int=10
)::Vector{Int}
    try
        # Get region containing this theorem
        region = get_comprehension_region(theorem_id, comprehension)

        if isempty(region.theorems)
            @warn "No comprehension region found for theorem $theorem_id"
            return Int[]
        end

        # Get all theorems in region except the target
        # Use comprehension instead of filter for zero-allocation optimization
        candidate_theorems = [t for t in region.theorems if t != theorem_id]

        if isempty(candidate_theorems)
            return Int[]
        end

        # Sample with weighting by co-visitation
        return sample_theorems_by_covisitation(
            theorem_id,
            candidate_theorems,
            comprehension,
            num_to_discover
        )
    catch e
        @warn "Theorem discovery failed: $e"
        return Int[]
    end
end

"""
    sample_theorems_by_covisitation(theorem_id::Int, candidate_theorems::Vector{Int},
                                    comprehension::Dict, num_to_sample::Int) -> Vector{Int}

Sample theorems weighted by their co-visitation score with the target theorem.
Higher co-visitation = higher sampling probability.
"""
function sample_theorems_by_covisitation(
    theorem_id::Int,
    candidate_theorems::Vector{Int},
    comprehension::Dict,
    num_to_sample::Int
)::Vector{Int}
    try
        co_visit_matrix = comprehension[:co_visit_matrix]

        # Get co-visitation scores for candidates
        scores = Float64[]
        for theorem in candidate_theorems
            if theorem_id <= size(co_visit_matrix, 1) && theorem <= size(co_visit_matrix, 2)
                score = co_visit_matrix[theorem_id, theorem]
            else
                score = 0.5  # Default score if out of bounds
            end
            push!(scores, max(score, 0.01))  # Ensure non-zero for sampling
        end

        # Sample with weights (without replacement)
        num_actual_sample = min(num_to_sample, length(candidate_theorems))
        sampled_theorems = sample_with_weights(candidate_theorems, scores, num_actual_sample)

        # Sort by co-visitation score (highest first)
        sampled_scores = Float64[]
        for theorem in sampled_theorems
            if theorem_id <= size(comprehension[:co_visit_matrix], 1) &&
               theorem <= size(comprehension[:co_visit_matrix], 2)
                score = comprehension[:co_visit_matrix][theorem_id, theorem]
            else
                score = 0.5
            end
            push!(sampled_scores, score)
        end

        sorted_indices = sortperm(sampled_scores, rev=true)
        return sampled_theorems[sorted_indices]
    catch e
        @warn "Co-visitation sampling failed: $e"
        # Fallback: return first few candidates
        return candidate_theorems[1:min(length(candidate_theorems), num_to_sample)]
    end
end

# ============================================================================
# Part 5: Session Management
# ============================================================================

"""
    start_discovery_session(theorem_id::Int, comprehension::Dict, gap::Float64) -> DiscoverySession

Start a new comprehension discovery session for a theorem.
"""
function start_discovery_session(
    theorem_id::Int,
    comprehension::Dict,
    gap::Float64
)::DiscoverySession
    region = get_comprehension_region(theorem_id, comprehension)

    discovered = discover_related_theorems(theorem_id, comprehension, num_to_discover=10)

    scores = Float64[]
    for theorem in discovered
        if theorem_id <= size(comprehension[:co_visit_matrix], 1) &&
           theorem <= size(comprehension[:co_visit_matrix], 2)
            score = comprehension[:co_visit_matrix][theorem_id, theorem]
        else
            score = 0.5
        end
        push!(scores, score)
    end

    return DiscoverySession(
        "discovery_$(theorem_id)_$(floor(Int, time()*1000))",
        theorem_id,
        region,
        discovered,
        scores,
        time(),
        gap
    )
end

"""
    get_region_statistics(region::ComprehensionRegion) -> Dict

Get statistics about a comprehension region.
"""
function get_region_statistics(region::ComprehensionRegion)::Dict
    centrality_values = collect(values(region.centrality))

    return Dict(
        :region_id => region.region_id,
        :num_theorems => region.size,
        :min_centrality => region.min_covisit,
        :max_centrality => region.max_covisit,
        :mean_centrality => mean(centrality_values),
        :std_centrality => std(centrality_values)
    )
end

# ============================================================================
# Part 6: Integration with Health Monitoring
# ============================================================================

"""
    get_discovery_recommendation(session::DiscoverySession, health_status) -> Dict

Get recommendation for next theorem to attempt based on:
- Comprehension region discovery
- Co-visitation scores
- Current system health
"""
function get_discovery_recommendation(session::DiscoverySession, health_status)::Dict
    if isempty(session.discovered_theorems)
        return Dict(
            :recommendation => "No theorems discovered",
            :theorems => Int[],
            :scores => Float64[]
        )
    end

    # Adjust priority based on health
    health_factor = if health_status.healthy
        1.0
    elseif health_status.degraded
        0.7
    else
        0.0
    end

    # Scale co-visitation scores by health
    adjusted_scores = session.covisitation_scores .* health_factor

    return Dict(
        :recommendation => "Use comprehension region $(session.region.region_id)",
        :theorems => session.discovered_theorems,
        :scores => session.covisitation_scores,
        :adjusted_scores => adjusted_scores,
        :health_factor => health_factor,
        :num_candidates => length(session.discovered_theorems)
    )
end

end  # module ComprehensionDiscovery
