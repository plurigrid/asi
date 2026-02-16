"""
    mobius_filter.jl

Week 2: Möbius Inversion Path Filtering
========================================

Identifies tangled geodesics via Möbius inversion: μ(n) ∈ {-1, 0, +1}
based on prime factorization of path lengths.

μ = +1  : prime paths (keep)
μ = -1  : odd-composite paths (rewrite needed)
μ = 0   : squared-factor paths (completely tangled, remove)
"""

using LinearAlgebra

module MobiusFilter

export enumerate_paths, mobius_weight, generate_filter_report

function enumerate_paths(adjacency::Matrix, max_length=4)
    n = size(adjacency, 1)
    paths = []
    
    for start in 1:n
        visited = Set([start])
        queue = [(start, [start], 1)]
        
        while !isempty(queue)
            current, path, depth = popfirst!(queue)
            
            if depth < max_length
                for next in 1:n
                    if adjacency[current, next] > 0.5 && !(next in visited)
                        new_visited = copy(visited)
                        push!(new_visited, next)
                        new_path = vcat(path, [next])
                        push!(paths, (new_path, length(new_path)))
                        push!(queue, (next, new_path, depth + 1))
                    end
                end
            end
        end
    end
    
    return paths
end

function factor_number(n::Int)
    if n <= 1
        return Int[]
    end
    factors = Int[]
    d = 2
    while d * d <= n
        while n % d == 0
            push!(factors, d)
            n = div(n, d)
        end
        d += 1
    end
    if n > 1
        push!(factors, n)
    end
    return factors
end

function mobius_weight(path::Vector{Int})
    path_length = length(path)
    
    if path_length <= 1
        return 1.0
    end
    
    factors = factor_number(path_length)
    
    if isempty(factors)
        return 1.0
    end
    
    if any(count(x -> x == f, factors) > 1 for f in unique(factors))
        return 0.0
    end
    
    return (-1.0)^length(factors)
end

function filter_tangled_paths(adjacency::Matrix, max_length=4)
    paths = enumerate_paths(adjacency, max_length)
    
    prime_paths = []
    tangled_paths = []
    
    for (path, length) in paths
        weight = mobius_weight(path)
        
        if weight > 0.5
            push!(prime_paths, (path, weight))
        else
            push!(tangled_paths, (path, weight))
        end
    end
    
    return prime_paths, tangled_paths
end

function generate_filter_report(adjacency::Matrix)
    prime_paths, tangled_paths = filter_tangled_paths(adjacency, 4)
    
    total_paths = length(prime_paths) + length(tangled_paths)
    
    report = """
╔════════════════════════════════════════════════════════════════════════╗
║                    MÖBIUS PATH FILTER REPORT                          ║
║                      Week 2: Tangle Detection                          ║
║                      Generated: Dec 22, 2025                           ║
╚════════════════════════════════════════════════════════════════════════╝

PATHS ENUMERATED AND CLASSIFIED
═════════════════════════════════════════════════════════════════════════

Total Paths Found:         $total_paths

Classification:
  Prime Paths (μ=+1):      $(length(prime_paths))
    └─ These are good - no changes needed
  
  Tangled Paths (μ=-1,0):  $(length(tangled_paths))
    └─ These have cycles and redundancies

TANGLED PATH ANALYSIS
═════════════════════════════════════════════════════════════════════════

Paths with negative or zero Möbius weight indicate:
  - μ = -1: Odd-composite path length (needs cycle breaking)
  - μ = 0:  Squared prime factors (completely tangled, consider removal)

Total Tangled: $(length(tangled_paths))

RECOMMENDATIONS
═════════════════════════════════════════════════════════════════════════

"""
    
    if length(tangled_paths) == 0
        report *= "✓ No tangled paths detected. System is clean.\n"
    else
        report *= "✗ Tangled paths found. Next steps:\n"
        report *= "  1. Analyze which edges are \"critical\" vs \"redundant\"\n"
        report *= "  2. Remove redundant edges (Week 4: safe_rewriting.jl)\n"
        report *= "  3. For odd-composite paths: break cycles via intermediate theorems\n"
        report *= "  4. Re-measure gap after modifications\n"
    end
    
    report *= "\n═════════════════════════════════════════════════════════════════════════\n"
    return report
end

end

if abspath(PROGRAM_FILE) == @__FILE__
    using .MobiusFilter
    using LinearAlgebra
    
    println("\n🔬 Spectral Architecture - Week 2: Möbius Path Filtering\n")
    
    # Test with simple graph
    adjacency = [
        0 1 1 0 0
        1 0 1 1 0
        1 1 0 1 1
        0 1 1 0 1
        0 0 1 1 0
    ]
    
    report = MobiusFilter.generate_filter_report(Float64.(adjacency))
    println(report)
end
