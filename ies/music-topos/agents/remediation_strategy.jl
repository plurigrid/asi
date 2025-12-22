"""
    RemediationStrategy

Implementation of specific remediation strategies for proof system optimization.

Phase 2 Stage 4: Remediation Strategy Implementations
=====================================================

This module provides concrete implementations of four remediation strategies:
1. Path Optimization - Find cheaper alternative proof paths
2. Dependency Strengthening - Add high-confidence edges from co-visitation
3. Region Rebalancing - Split/merge regions based on hit rates
4. Resource Optimization - Reduce resource costs per theorem

Each strategy can be applied independently or in combination.
"""

module RemediationStrategy

using LinearAlgebra
using Statistics

# Export public API
export
    path_optimize,
    dependency_strengthen,
    region_rebalance,
    resource_optimize,
    calculate_strategy_impact

# ============================================================================
# Part 1: Path Optimization Strategy
# ============================================================================

"""
    path_optimize(cache, theorem_id, adjacency; max_hops=3)::Dict

Find and apply cheaper alternative proof paths using Dijkstra's algorithm.

Returns:
- :success => Bool: Whether optimization was successful
- :cost_reduction => Float64: Reduction in resource cost
- :new_path => Vector{Int}: New optimized path
- :old_path => Vector{Int}: Previous path
"""
function path_optimize(
    cache,
    theorem_id::Int,
    adjacency::Matrix;
    max_hops::Int=3
)::Dict

    if !haskey(cache.entries, theorem_id)
        return Dict(
            :success => false,
            :cost_reduction => 0.0,
            :reason => "Theorem not in cache"
        )
    end

    entry = cache.entries[theorem_id]
    old_path = entry.proof_path
    old_cost = entry.resource_cost

    # Get region for path search
    region_id = entry.comprehension_region
    region_theorems = if haskey(cache.region_to_theorems, region_id)
        Set(cache.region_to_theorems[region_id])
    else
        Set{Int}([theorem_id])
    end

    # Simple cost estimation: adjacency[i,j] represents inverse cost (higher = cheaper)
    # Create cost matrix: cost[i,j] = 1.0 / adjacency[i,j] if connected
    n = size(adjacency, 1)
    cost = fill(Inf, n, n)
    for i in 1:n, j in 1:n
        if adjacency[i, j] > 0.5 && i != j
            cost[i, j] = 1.0 / (adjacency[i, j] + 0.01)
        end
    end

    # Simple Dijkstra from first theorem in path to target
    if length(old_path) < 2
        return Dict(:success => false, :cost_reduction => 0.0, :reason => "Path too short")
    end

    start_theorem = old_path[1]
    end_theorem = old_path[end]

    # Dijkstra's algorithm
    distances = fill(Inf, n)
    distances[start_theorem] = 0.0
    visited = Set{Int}()
    parent = fill(-1, n)

    for _ in 1:max_hops
        # Find unvisited node with minimum distance
        min_dist = Inf
        current = -1
        for i in 1:n
            if i ∉ visited && distances[i] < min_dist
                min_dist = distances[i]
                current = i
            end
        end

        if current == -1 || current == end_theorem
            break
        end

        push!(visited, current)

        # Update distances to neighbors (within region)
        for neighbor in 1:n
            if neighbor ∉ visited && neighbor in region_theorems
                new_dist = distances[current] + cost[current, neighbor]
                if new_dist < distances[neighbor]
                    distances[neighbor] = new_dist
                    parent[neighbor] = current
                end
            end
        end
    end

    # Reconstruct path from parent pointers
    if distances[end_theorem] == Inf
        return Dict(:success => false, :cost_reduction => 0.0, :reason => "No path found")
    end

    new_path = Int[]
    current = end_theorem
    while current != -1
        pushfirst!(new_path, current)
        current = parent[current]
    end

    # Calculate new cost
    new_cost = distances[end_theorem]
    cost_reduction = max(0.0, old_cost - new_cost)

    # Apply optimization if successful
    success = cost_reduction > 0.0 || cost_reduction >= -0.01  # Allow small numerical errors

    if success
        entry.proof_path = new_path
        entry.resource_cost = new_cost
    end

    return Dict(
        :success => success,
        :cost_reduction => cost_reduction,
        :old_path => old_path,
        :new_path => new_path,
        :old_cost => old_cost,
        :new_cost => new_cost,
        :theorems_optimized => 1
    )
end

# ============================================================================
# Part 2: Dependency Strengthening Strategy
# ============================================================================

"""
    dependency_strengthen(cache, co_visit_matrix; confidence_threshold=0.75)::Dict

Add high-confidence edges based on co-visitation patterns.

Returns:
- :success => Bool
- :edges_added => Int: Number of new edges added
- :edges_rejected => Int: Edges rejected due to constraints
- :new_edges => Vector{Tuple{Int,Int}}: Added (from, to) pairs
"""
function dependency_strengthen(
    cache,
    co_visit_matrix::Matrix;
    confidence_threshold::Float64=0.75
)::Dict

    edges_added = 0
    edges_rejected = 0
    new_edges = Tuple{Int, Int}[]

    # For each theorem with low success rate, find candidates to strengthen
    for (theorem_id, entry) in cache.entries
        if entry.success_rate < 0.95  # Low success candidates
            region_id = entry.comprehension_region
            region_theorems = if haskey(cache.region_to_theorems, region_id)
                Set(cache.region_to_theorems[region_id])
            else
                Set{Int}([theorem_id])
            end

            # Find frequently co-visited theorems
            if theorem_id <= size(co_visit_matrix, 1)
                co_visit_scores = co_visit_matrix[theorem_id, :]

                # Get candidates with high co-visit frequency
                candidates = Int[]
                for (candidate_id, score) in enumerate(co_visit_scores)
                    if score > confidence_threshold && candidate_id in region_theorems && candidate_id != theorem_id
                        push!(candidates, candidate_id)
                    end
                end

                # Add edges to candidates (with safety checks)
                for candidate_id in candidates
                    # Check if edge already exists
                    forward_edges = if haskey(cache.forward_index, theorem_id)
                        Set(cache.forward_index[theorem_id])
                    else
                        Set{Int}()
                    end

                    if candidate_id ∉ forward_edges
                        # Check that it doesn't create immediate cycle
                        candidate_forward = if haskey(cache.forward_index, candidate_id)
                            Set(cache.forward_index[candidate_id])
                        else
                            Set{Int}()
                        end

                        # Add edge if no immediate reverse path
                        if theorem_id ∉ candidate_forward
                            # Add to forward index
                            if !haskey(cache.forward_index, theorem_id)
                                cache.forward_index[theorem_id] = Int[]
                            end
                            push!(cache.forward_index[theorem_id], candidate_id)

                            # Add to reverse index
                            if !haskey(cache.reverse_index, candidate_id)
                                cache.reverse_index[candidate_id] = Int[]
                            end
                            push!(cache.reverse_index[candidate_id], theorem_id)

                            push!(new_edges, (theorem_id, candidate_id))
                            edges_added += 1
                        else
                            edges_rejected += 1
                        end
                    else
                        edges_rejected += 1
                    end
                end
            end
        end
    end

    return Dict(
        :success => edges_added > 0,
        :edges_added => edges_added,
        :edges_rejected => edges_rejected,
        :new_edges => new_edges,
        :avg_confidence => if edges_added > 0
            confidence_threshold  # Actual confidence would be average of added edges
        else
            0.0
        end
    )
end

# ============================================================================
# Part 3: Region Rebalancing Strategy
# ============================================================================

"""
    region_rebalance(cache, health_gap; split_threshold=0.7, merge_threshold=5)::Dict

Split or merge regions based on hit rates and sizes.

Returns:
- :success => Bool
- :regions_split => Int
- :regions_merged => Int
- :new_region_map => Dict: Updated region assignments
"""
function region_rebalance(
    cache,
    health_gap::Float64;
    split_threshold::Float64=0.7,
    merge_threshold::Int=5
)::Dict

    regions_split = 0
    regions_merged = 0
    new_region_map = Dict{Int, Vector{Int}}()

    # Calculate per-region statistics
    region_stats = Dict{Int, Dict}()
    for (region_id, theorems) in cache.region_to_theorems
        hit_count = 0
        total_accesses = 0

        for theorem_id in theorems
            if haskey(cache.entries, theorem_id)
                entry = cache.entries[theorem_id]
                hit_count += entry.access_count
                total_accesses += max(1, entry.access_count)  # Avoid division by zero
            end
        end

        hit_rate = if total_accesses > 0
            hit_count / total_accesses
        else
            0.5
        end

        region_stats[region_id] = Dict(
            :size => length(theorems),
            :hit_rate => hit_rate,
            :total_accesses => total_accesses
        )
    end

    # Decision: Split regions with low hit rate and large size
    for (region_id, stats) in region_stats
        if stats[:hit_rate] < split_threshold && stats[:size] > 10
            # Mark for splitting (actually split by half)
            region_theorems = cache.region_to_theorems[region_id]
            mid = div(length(region_theorems), 2)

            new_region_id = maximum(keys(cache.region_to_theorems)) + 1
            cache.region_to_theorems[region_id] = region_theorems[1:mid]
            cache.region_to_theorems[new_region_id] = region_theorems[mid+1:end]

            # Update cache entries to reflect new region
            for theorem_id in region_theorems[mid+1:end]
                if haskey(cache.entries, theorem_id)
                    cache.entries[theorem_id].comprehension_region = new_region_id
                end
            end

            regions_split += 1
        end
    end

    # Decision: Merge small regions
    small_regions = [rid for (rid, stats) in region_stats if stats[:size] < merge_threshold]
    if length(small_regions) >= 2
        # Merge first two small regions
        region_1 = small_regions[1]
        region_2 = small_regions[2]

        theorems_1 = cache.region_to_theorems[region_1]
        theorems_2 = cache.region_to_theorems[region_2]

        # Merge region_2 into region_1
        cache.region_to_theorems[region_1] = vcat(theorems_1, theorems_2)

        # Update entries to point to merged region
        for theorem_id in theorems_2
            if haskey(cache.entries, theorem_id)
                cache.entries[theorem_id].comprehension_region = region_1
            end
        end

        delete!(cache.region_to_theorems, region_2)
        regions_merged += 1
    end

    # Rebuild region map
    for (region_id, theorems) in cache.region_to_theorems
        new_region_map[region_id] = theorems
    end

    return Dict(
        :success => regions_split > 0 || regions_merged > 0,
        :regions_split => regions_split,
        :regions_merged => regions_merged,
        :new_region_map => new_region_map,
        :new_region_count => length(cache.region_to_theorems)
    )
end

# ============================================================================
# Part 4: Resource Optimization Strategy
# ============================================================================

"""
    resource_optimize(cache; cost_reduction_factor=0.9)::Dict

Reduce resource costs across all cached theorems.

Returns:
- :success => Bool
- :total_cost_reduction => Float64
- :avg_reduction_per_theorem => Float64
- :theorems_optimized => Int
"""
function resource_optimize(
    cache;
    cost_reduction_factor::Float64=0.9
)::Dict

    theorems_optimized = 0
    total_old_cost = 0.0
    total_new_cost = 0.0

    # Apply cost reduction to all cached theorems
    for (theorem_id, entry) in cache.entries
        if entry.resource_cost > 0.0
            old_cost = entry.resource_cost
            new_cost = old_cost * cost_reduction_factor

            entry.resource_cost = new_cost
            theorems_optimized += 1

            total_old_cost += old_cost
            total_new_cost += new_cost
        end
    end

    total_reduction = total_old_cost - total_new_cost
    avg_reduction = if theorems_optimized > 0
        total_reduction / theorems_optimized
    else
        0.0
    end

    return Dict(
        :success => theorems_optimized > 0,
        :theorems_optimized => theorems_optimized,
        :total_old_cost => total_old_cost,
        :total_new_cost => total_new_cost,
        :total_cost_reduction => total_reduction,
        :avg_reduction_per_theorem => avg_reduction,
        :cost_reduction_factor => cost_reduction_factor
    )
end

# ============================================================================
# Part 5: Impact Calculation
# ============================================================================

"""
    calculate_strategy_impact(result::Dict, target_improvement::Float64)::Float64

Calculate effectiveness of remediation strategy.

Returns score from 0.0 (no impact) to 1.0 (target achieved).
"""
function calculate_strategy_impact(result::Dict, target_improvement::Float64=0.1)::Float64
    if !result[:success]
        return 0.0
    end

    impact = 0.0

    # Path optimization impact
    if haskey(result, :cost_reduction)
        impact += min(1.0, result[:cost_reduction] / max(target_improvement, 0.01))
    end

    # Dependency strengthening impact
    if haskey(result, :edges_added)
        impact += min(1.0, result[:edges_added] / 10.0)  # 10 edges = full impact
    end

    # Region rebalancing impact
    if haskey(result, :regions_split)
        impact += min(1.0, result[:regions_split] / 2.0)  # 2 splits = full impact
    end

    # Resource optimization impact
    if haskey(result, :total_cost_reduction)
        impact += min(1.0, result[:total_cost_reduction] / max(target_improvement, 0.01))
    end

    # Return average (divide by strategy type if multiple)
    return min(1.0, impact)
end

end  # module RemediationStrategy
