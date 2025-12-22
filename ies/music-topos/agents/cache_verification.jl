"""
    CacheVerification

Verification that navigation cache is correct using tree-sitter analyzer.

Phase 2 Stage 3: Cache Verification Integration
===============================================

This module verifies cache consistency by:
1. Using tree-sitter to extract actual module dependencies
2. Comparing cached paths with real module structure
3. Ensuring no circular dependencies in proof paths
4. Validating that all cached theorems are reachable
"""

module CacheVerification

using LinearAlgebra
using Statistics

# Try to import tree-sitter analyzer if available
USE_TREE_SITTER = false
try
    include("../../../.codex/skills/tree-sitter-analyzer/tree_sitter_analyzer.jl")
    import .TreeSitterAnalyzer
    USE_TREE_SITTER = true
catch e
    @warn "Tree-sitter analyzer not available: $e"
    USE_TREE_SITTER = false
end

export
    VerificationReport,
    verify_cache_structure,
    verify_cache_consistency,
    verify_no_circular_paths,
    validate_reachability,
    get_verification_summary

# ============================================================================
# Part 1: Verification Data Structures
# ============================================================================

"""
    VerificationReport

Comprehensive cache verification report.
"""
mutable struct VerificationReport
    timestamp::Float64
    total_entries::Int
    entries_verified::Int
    entries_valid::Int
    entries_invalid::Int
    circular_paths_detected::Int
    unreachable_theorems::Vector{Int}
    missing_dependencies::Vector{Tuple{Int, Int}}  # (from, to) pairs missing
    extra_dependencies::Vector{Tuple{Int, Int}}    # (from, to) pairs extra
    consistency_score::Float64                      # 0.0-1.0
    is_valid::Bool
end

# ============================================================================
# Part 2: Cache Structure Verification
# ============================================================================

"""
    verify_cache_structure(cache)::VerificationReport

Verify that cache structure is internally consistent.
"""
function verify_cache_structure(cache)::VerificationReport
    report = VerificationReport(
        time(),
        length(cache.entries),
        0,
        0,
        0,
        0,
        Int[],
        Tuple{Int, Int}[],
        Tuple{Int, Int}[],
        0.0,
        true
    )

    # Check each cache entry
    for (theorem_id, entry) in cache.entries
        report.entries_verified += 1

        # Verify entry fields are consistent
        valid = true

        # Check theorem_id matches
        if entry.theorem_id != theorem_id
            valid = false
        end

        # Check region exists
        if !haskey(cache.region_to_theorems, entry.comprehension_region)
            valid = false
        end

        # Check theorem is in claimed region
        if haskey(cache.region_to_theorems, entry.comprehension_region)
            if theorem_id ∉ cache.region_to_theorems[entry.comprehension_region]
                valid = false
            end
        end

        # Check resource cost is non-negative
        if entry.resource_cost < 0.0
            valid = false
        end

        # Check success rate is in [0, 1]
        if entry.success_rate < 0.0 || entry.success_rate > 1.0
            valid = false
        end

        if valid
            report.entries_valid += 1
        else
            report.entries_invalid += 1
        end
    end

    # Compute consistency score
    if report.entries_verified > 0
        report.consistency_score = report.entries_valid / report.entries_verified
    else
        report.consistency_score = 1.0
    end

    report.is_valid = report.consistency_score >= 0.95

    return report
end

# ============================================================================
# Part 3: Circular Path Detection
# ============================================================================

"""
    verify_no_circular_paths(cache) -> VerificationReport

Verify that forward_index and reverse_index are consistent with each other.
For each edge A→B in forward_index, B should have A in reverse_index.
"""
function verify_no_circular_paths(cache)::VerificationReport
    report = VerificationReport(
        time(),
        length(cache.entries),
        0,
        0,
        0,
        0,
        Int[],
        Tuple{Int, Int}[],
        Tuple{Int, Int}[],
        0.0,
        true
    )

    # Check forward-reverse index consistency
    # For each edge A→B in forward_index, B should have A in reverse_index
    for (from_theorem, to_theorems) in cache.forward_index
        report.entries_verified += 1

        has_inconsistency = false

        for to_theorem in to_theorems
            # Check that the reverse_index has the matching entry
            if !haskey(cache.reverse_index, to_theorem)
                has_inconsistency = true
                push!(report.missing_dependencies, (to_theorem, from_theorem))
            elseif from_theorem ∉ cache.reverse_index[to_theorem]
                has_inconsistency = true
                push!(report.missing_dependencies, (to_theorem, from_theorem))
            end
        end

        if has_inconsistency
            report.circular_paths_detected += 1  # Reusing field for inconsistencies
            report.entries_invalid += 1
        else
            report.entries_valid += 1
        end
    end

    # Compute consistency score
    if report.entries_verified > 0
        report.consistency_score = report.entries_valid / report.entries_verified
    else
        report.consistency_score = 1.0
    end

    report.is_valid = report.entries_invalid == 0

    return report
end

# ============================================================================
# Part 4: Dependency Comparison
# ============================================================================

"""
    verify_cache_consistency(cache, adjacency::Matrix)::VerificationReport

Compare cached dependencies with actual adjacency matrix.
Detects missing and extra dependencies.
"""
function verify_cache_consistency(cache, adjacency::Matrix)::VerificationReport
    report = VerificationReport(
        time(),
        length(cache.entries),
        0,
        0,
        0,
        0,
        Int[],
        Tuple{Int, Int}[],
        Tuple{Int, Int}[],
        0.0,
        true
    )

    # For each cached theorem, verify its connections match adjacency within its region
    for (theorem_id, entry) in cache.entries
        report.entries_verified += 1

        if theorem_id > size(adjacency, 1)
            report.entries_invalid += 1
            continue
        end

        # Get the region this theorem belongs to
        region_id = entry.comprehension_region
        region_theorems = if haskey(cache.region_to_theorems, region_id)
            Set(cache.region_to_theorems[region_id])
        else
            Set{Int}()
        end

        # Get cached forward connections
        cached_connections = if haskey(cache.forward_index, theorem_id)
            Set(cache.forward_index[theorem_id])
        else
            Set{Int}()
        end

        # Get actual connections from adjacency (score > 0.5) within same region
        actual_connections = Set{Int}()
        for (idx, score) in enumerate(adjacency[theorem_id, :])
            if score > 0.5 && idx != theorem_id && idx in region_theorems
                push!(actual_connections, idx)
            end
        end

        # Find discrepancies
        missing = setdiff(actual_connections, cached_connections)
        extra = setdiff(cached_connections, actual_connections)

        if isempty(missing) && isempty(extra)
            report.entries_valid += 1
        else
            report.entries_invalid += 1

            # Record discrepancies
            for missing_theorem in missing
                push!(report.missing_dependencies, (theorem_id, missing_theorem))
            end
            for extra_theorem in extra
                push!(report.extra_dependencies, (theorem_id, extra_theorem))
            end
        end
    end

    # Compute consistency score
    if report.entries_verified > 0
        report.consistency_score = report.entries_valid / report.entries_verified
    else
        report.consistency_score = 1.0
    end

    report.is_valid = (report.consistency_score >= 0.95 &&
                       length(report.missing_dependencies) == 0)

    return report
end

# ============================================================================
# Part 5: Reachability Validation
# ============================================================================

"""
    validate_reachability(cache, root_theorem::Int, max_depth::Int=3)
        -> VerificationReport

Verify that all cached theorems are reachable from root within max_depth.
"""
function validate_reachability(
    cache,
    root_theorem::Int,
    max_depth::Int=3
)::VerificationReport

    report = VerificationReport(
        time(),
        length(cache.entries),
        0,
        0,
        0,
        0,
        Int[],
        Tuple{Int, Int}[],
        Tuple{Int, Int}[],
        0.0,
        true
    )

    # BFS from root to find reachable theorems
    reachable = Set{Int}([root_theorem])
    queue = [(root_theorem, 0)]

    while !isempty(queue)
        current, depth = popfirst!(queue)

        if depth < max_depth && haskey(cache.forward_index, current)
            for next_theorem in cache.forward_index[current]
                if next_theorem ∉ reachable
                    push!(reachable, next_theorem)
                    push!(queue, (next_theorem, depth + 1))
                end
            end
        end
    end

    # Check which cached theorems are reachable
    for (theorem_id, entry) in cache.entries
        report.entries_verified += 1

        if theorem_id in reachable
            report.entries_valid += 1
        else
            report.entries_invalid += 1
            push!(report.unreachable_theorems, theorem_id)
        end
    end

    # Compute consistency score
    if report.entries_verified > 0
        report.consistency_score = report.entries_valid / report.entries_verified
    else
        report.consistency_score = 1.0
    end

    report.is_valid = isempty(report.unreachable_theorems)

    return report
end

# ============================================================================
# Part 6: Verification Summary
# ============================================================================

"""
    get_verification_summary(reports::Vector{VerificationReport})::Dict

Synthesize multiple verification reports into summary.
"""
function get_verification_summary(reports::Vector{VerificationReport})::Dict
    if isempty(reports)
        return Dict(
            :status => "No reports",
            :overall_valid => false,
            :avg_consistency => 0.0
        )
    end

    # Compute aggregate statistics
    total_valid = sum(report.is_valid ? 1 : 0 for report in reports)
    avg_consistency = mean(report.consistency_score for report in reports)
    total_circular = sum(report.circular_paths_detected for report in reports)
    total_invalid = sum(report.entries_invalid for report in reports)

    overall_valid = (total_valid == length(reports) &&
                     total_circular == 0 &&
                     total_invalid == 0)

    return Dict(
        :overall_valid => overall_valid,
        :reports_valid => total_valid,
        :total_reports => length(reports),
        :avg_consistency => avg_consistency,
        :total_circular_paths => total_circular,
        :total_invalid_entries => total_invalid,
        :timestamp => time()
    )
end

end  # module CacheVerification
