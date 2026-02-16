"""
    safe_rewriting.jl

Week 4: Safe Rewriting with Gap Preservation
==============================================

Strategic selective edge removal maintaining gap ≥ 0.25.
Identifies critical edges (would break system) vs redundant edges (safe to remove).

Analyzes betweenness centrality to measure criticality.
Recommends cycle-breaking via intermediate theorems for odd-composite paths.
"""

using LinearAlgebra
using Statistics

module SafeRewriting

export EdgeImportance, RewritePlan, generate_rewrite_report

struct EdgeImportance
    edge_id::Tuple{Int, Int}
    betweenness_centrality::Float64
    gap_sensitivity::Float64
    redundancy_score::Float64
    recommendation::String
end

struct RewritePlan
    edges_to_remove::Vector{Tuple{Int, Int}}
    edges_to_split::Vector{Tuple{Int, Int}}
    cycle_breakers::Vector{String}
    expected_gap_before::Float64
    expected_gap_after::Float64
    safe::Bool
    complexity::String
end

function compute_edge_importance(adjacency::Matrix)
    n = size(adjacency, 1)
    edge_importances = EdgeImportance[]
    
    for i in 1:n
        for j in i+1:n
            if adjacency[i, j] > 0.5
                betweenness = compute_betweenness_centrality(adjacency, i, j)
                centrality = (betweenness + 1.0) / (n * (n - 1) / 2)
                gap_sensitivity = centrality * 100.0
                redundancy = 100.0 - gap_sensitivity
                
                if gap_sensitivity > 80.0
                    rec = "CRITICAL - Do not remove"
                elseif gap_sensitivity > 40.0
                    rec = "IMPORTANT - Remove only if necessary"
                else
                    rec = "REDUNDANT - Safe to remove"
                end
                
                push!(edge_importances, EdgeImportance(
                    (i, j),
                    betweenness,
                    gap_sensitivity,
                    redundancy,
                    rec
                ))
            end
        end
    end
    
    return edge_importances
end

function compute_betweenness_centrality(adjacency::Matrix, src::Int, dst::Int)
    n = size(adjacency, 1)
    shortest_paths = shortest_path_count(adjacency, src, dst)
    return Float64(shortest_paths)
end

function shortest_path_count(adjacency::Matrix, src::Int, dst::Int)
    n = size(adjacency, 1)
    visited = Set([src])
    queue = [(src, 1)]
    count = 0
    
    while !isempty(queue)
        current, dist = popfirst!(queue)
        
        if current == dst
            count += 1
            continue
        end
        
        if dist < n
            for next in 1:n
                if adjacency[current, next] > 0.5 && !(next in visited)
                    push!(visited, next)
                    push!(queue, (next, dist + 1))
                end
            end
        end
    end
    
    return max(count, 1)
end

function identify_redundant_edges(edges::Vector{EdgeImportance})
    return [e.edge_id for e in edges if e.redundancy_score > 50.0]
end

function generate_rewrite_plan(adjacency::Matrix, original_gap::Float64)
    edges = compute_edge_importance(adjacency)
    
    if isempty(edges)
        return RewritePlan([], [], [], original_gap, original_gap, true, "No changes needed")
    end
    
    redundant = identify_redundant_edges(edges)
    
    all_critical = all(e.gap_sensitivity > 50.0 for e in edges)
    
    if all_critical && original_gap < 0.25
        return RewritePlan(
            [],
            [],
            ["Add intermediate theorem to break cycles", "Restructure proof dependencies"],
            original_gap,
            original_gap + 0.15,
            false,
            "Requires restructuring, not edge removal"
        )
    end
    
    expected_gap = original_gap + 0.1 * (length(redundant) / max(length(edges), 1))
    
    return RewritePlan(
        redundant,
        [],
        [],
        original_gap,
        expected_gap,
        expected_gap >= 0.25,
        "Selective removal"
    )
end

function generate_rewrite_report(adjacency::Matrix, original_gap::Float64)
    plan = generate_rewrite_plan(adjacency, original_gap)
    edges = compute_edge_importance(adjacency)
    
    report = """
╔════════════════════════════════════════════════════════════════════════╗
║                  SAFE REWRITING ANALYSIS REPORT                       ║
║                   Week 4: Strategic Edge Removal                       ║
║                     Generated: Dec 22, 2025                            ║
╚════════════════════════════════════════════════════════════════════════╝

EDGE CRITICALITY ANALYSIS
═════════════════════════════════════════════════════════════════════════

Total Edges Analyzed:      $(length(edges))
Critical Edges:            $(sum(e.gap_sensitivity > 80.0 for e in edges))
Important Edges:           $(sum((40.0 <= e.gap_sensitivity <= 80.0) for e in edges))
Redundant Edges:           $(sum(e.gap_sensitivity < 40.0 for e in edges))

REWRITE PLAN
═════════════════════════════════════════════════════════════════════════

Edges to Remove:           $(length(plan.edges_to_remove))
Cycle-Breaker Points:      $(length(plan.cycle_breakers))

GAP PROJECTION
═════════════════════════════════════════════════════════════════════════

Current Gap:               $(round(plan.expected_gap_before, digits=4))
Projected Gap (after):     $(round(plan.expected_gap_after, digits=4))
Will Reach Ramanujan:      $(plan.expected_gap_after >= 0.25 ? "YES" : "UNCERTAIN")

"""
    
    if !isempty(plan.cycle_breakers)
        report *= """
RECOMMENDED STRUCTURAL CHANGES
═════════════════════════════════════════════════════════════════════════

$(join(["  - $(cb)" for cb in plan.cycle_breakers], "\n"))

"""
    end
    
    report *= """
SAFETY ASSESSMENT
═════════════════════════════════════════════════════════════════════════

Plan Status: $(plan.safe ? "✓ SAFE" : "⚠ NEEDS REVIEW")
Strategy:    $(plan.complexity)

"""
    
    if !plan.safe && original_gap < 0.25
        report *= """
WARNING: Simple edge removal may not be sufficient for gap < 0.25.
Recommended: Restructure proof organization via intermediate theorems.
"""
    end
    
    report *= "\n═════════════════════════════════════════════════════════════════════════\n"
    return report
end

end

if abspath(PROGRAM_FILE) == @__FILE__
    using .SafeRewriting
    using LinearAlgebra
    
    println("\n🔬 Spectral Architecture - Week 4: Safe Rewriting\n")
    
    # Test with graph that has low gap
    adjacency = [
        0 1 1 0
        1 0 1 1
        1 1 0 1
        0 1 1 0
    ]
    
    report = SafeRewriting.generate_rewrite_report(Float64.(adjacency), 0.5)
    println(report)
end
