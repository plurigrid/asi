#!/usr/bin/env julia
"""
Spectral Embedding Learner - Julia Implementation with Gay.jl Integration

Self-learning topological embedding with configurable gamut for optimal
spectral gap and fast mixing random walks on expander structures.
"""

using LinearAlgebra
using Random

# Gay.jl-compatible color generation
module GayCompat
    using Random
    
    const PHI = (1 + sqrt(5)) / 2
    const GOLDEN_ANGLE = 360.0 / (PHI^2)  # ~137.508°
    
    mutable struct SplitMix64
        state::UInt64
    end
    
    function next!(rng::SplitMix64)::UInt64
        rng.state += 0x9e3779b97f4a7c15
        z = rng.state
        z = (z ⊻ (z >> 30)) * 0xbf58476d1ce4e5b9
        z = (z ⊻ (z >> 27)) * 0x94d049bb133111eb
        return z ⊻ (z >> 31)
    end
    
    function split(rng::SplitMix64)::Tuple{SplitMix64, SplitMix64}
        s1 = next!(rng)
        s2 = next!(rng)
        return (SplitMix64(s1), SplitMix64(s2))
    end
    
    function hue_at(seed::Int, idx::Int)::Float64
        rng = SplitMix64(UInt64(seed))
        for _ in 1:idx
            next!(rng)
        end
        return mod(next!(rng) / typemax(UInt64) * 360 + idx * GOLDEN_ANGLE, 360)
    end
    
    function trit_at(seed::Int, idx::Int)::Int
        rng = SplitMix64(UInt64(seed))
        for _ in 1:idx
            next!(rng)
        end
        return mod(Int(next!(rng)), 3) - 1  # -1, 0, +1
    end
    
    function hex_at(seed::Int, idx::Int)::String
        h = hue_at(seed, idx)
        # HSL to RGB (S=0.7, L=0.55)
        s, l = 0.7, 0.55
        c = (1 - abs(2l - 1)) * s
        x = c * (1 - abs(mod(h/60, 2) - 1))
        m = l - c/2
        
        r, g, b = if h < 60
            (c, x, 0.0)
        elseif h < 120
            (x, c, 0.0)
        elseif h < 180
            (0.0, c, x)
        elseif h < 240
            (0.0, x, c)
        elseif h < 300
            (x, 0.0, c)
        else
            (c, 0.0, x)
        end
        
        ri = round(Int, (r + m) * 255)
        gi = round(Int, (g + m) * 255)
        bi = round(Int, (b + m) * 255)
        
        return "#" * uppercase(string(ri, base=16, pad=2) * 
                               string(gi, base=16, pad=2) * 
                               string(bi, base=16, pad=2))
    end
end

struct SpectralMetrics
    gap::Float64
    lambda_2::Float64
    mixing_time::Float64
    gap_efficiency::Float64
    is_ramanujan::Bool
end

struct EdgeLearningStep
    node::Int
    edges_added::Vector{Tuple{Int,Int}}
    gap_before::Float64
    gap_after::Float64
    ramanujan_preserved::Bool
end

mutable struct SpectralEmbeddingLearner
    seed::Int
    p::Int  # gamut prime
    d::Int  # target degree
    target_efficiency::Float64
    
    embeddings::Dict{Int, Vector{Float64}}
    adjacency::Dict{Int, Set{Int}}
    history::Vector{EdgeLearningStep}
    
    function SpectralEmbeddingLearner(;
        seed::Int = 1069,
        gamut_prime::Int = 3,
        target_degree::Int = 4,
        target_efficiency::Float64 = 0.95
    )
        Random.seed!(seed)
        new(seed, gamut_prime, target_degree, target_efficiency,
            Dict{Int, Vector{Float64}}(),
            Dict{Int, Set{Int}}(),
            EdgeLearningStep[])
    end
end

n_vertices(L::SpectralEmbeddingLearner) = length(L.embeddings)
ramanujan_bound(L::SpectralEmbeddingLearner) = 2 * sqrt(L.d - 1)
optimal_gap(L::SpectralEmbeddingLearner) = L.d - ramanujan_bound(L)

function gamut_depth(L::SpectralEmbeddingLearner, n::Int = n_vertices(L))
    n > 0 ? ceil(Int, log(L.p, n)) : 0
end

function p_adic_valuation(n::Int, p::Int)
    n == 0 && return typemax(Int)
    k = 0
    while n % p == 0
        n ÷= p
        k += 1
    end
    return k
end

function p_adic_norm(n::Int, p::Int)
    v = p_adic_valuation(n, p)
    v == typemax(Int) ? 0.0 : Float64(p)^(-v)
end

function p_adic_distance(L::SpectralEmbeddingLearner, a::Vector{Float64}, b::Vector{Float64})
    scale = 2^20
    diff_int = round.(Int, (a .- b) .* scale)
    norms = [d != 0 ? p_adic_norm(abs(d), L.p) : 0.0 for d in diff_int]
    return maximum(norms; init=0.0)
end

function adjacency_matrix(L::SpectralEmbeddingLearner)
    n = n_vertices(L)
    A = zeros(n, n)
    for (u, neighbors) in L.adjacency
        for v in neighbors
            A[u+1, v+1] = 1.0
            A[v+1, u+1] = 1.0
        end
    end
    return A
end

function eigenvalues(L::SpectralEmbeddingLearner)
    n = n_vertices(L)
    n < 2 && return [0.0]
    A = adjacency_matrix(L)
    eigs = eigvals(Symmetric(A))
    return sort(eigs, rev=true)
end

second_eigenvalue(L::SpectralEmbeddingLearner) = begin
    eigs = eigenvalues(L)
    length(eigs) > 1 ? eigs[2] : 0.0
end

function spectral_gap(L::SpectralEmbeddingLearner)
    eigs = eigenvalues(L)
    length(eigs) < 2 ? 0.0 : eigs[1] - eigs[2]
end

function gap_efficiency(L::SpectralEmbeddingLearner)
    opt = optimal_gap(L)
    opt <= 0 ? 0.0 : min(spectral_gap(L) / opt, 1.0)
end

is_ramanujan(L::SpectralEmbeddingLearner) = second_eigenvalue(L) <= ramanujan_bound(L) + 1e-10

function mixing_time(L::SpectralEmbeddingLearner)
    gap = spectral_gap(L)
    gap <= 0 ? Inf : log(max(n_vertices(L), 1)) / gap
end

function metrics(L::SpectralEmbeddingLearner)
    SpectralMetrics(
        spectral_gap(L),
        second_eigenvalue(L),
        mixing_time(L),
        gap_efficiency(L),
        is_ramanujan(L)
    )
end

function add_edge!(L::SpectralEmbeddingLearner, u::Int, v::Int)
    haskey(L.adjacency, u) || (L.adjacency[u] = Set{Int}())
    haskey(L.adjacency, v) || (L.adjacency[v] = Set{Int}())
    push!(L.adjacency[u], v)
    push!(L.adjacency[v], u)
end

function remove_edge!(L::SpectralEmbeddingLearner, u::Int, v::Int)
    haskey(L.adjacency, u) && delete!(L.adjacency[u], v)
    haskey(L.adjacency, v) && delete!(L.adjacency[v], u)
end

function test_edge_preserves_ramanujan(L::SpectralEmbeddingLearner, u::Int, v::Int)
    add_edge!(L, u, v)
    lam2 = second_eigenvalue(L)
    preserves = lam2 <= ramanujan_bound(L) + 1e-10
    remove_edge!(L, u, v)
    return preserves, lam2
end

function padic_candidates(L::SpectralEmbeddingLearner, node_id::Int, k::Int)
    !haskey(L.embeddings, node_id) && return Tuple{Int,Int}[]
    
    emb = L.embeddings[node_id]
    distances = Tuple{Int, Float64}[]
    
    for other in keys(L.embeddings)
        other == node_id && continue
        other in get(L.adjacency, node_id, Set{Int}()) && continue
        d = p_adic_distance(L, emb, L.embeddings[other])
        push!(distances, (other, d))
    end
    
    sort!(distances, by=x->x[2])
    return [(node_id, other) for (other, _) in distances[1:min(k, length(distances))]]
end

function add_node!(L::SpectralEmbeddingLearner, embedding::Vector{Float64})
    node_id = n_vertices(L)
    L.embeddings[node_id] = embedding
    L.adjacency[node_id] = Set{Int}()
    
    if node_id == 0
        push!(L.history, EdgeLearningStep(0, [], 0.0, 0.0, true))
        return node_id
    end
    
    gap_before = spectral_gap(L)
    candidates = padic_candidates(L, node_id, L.d * 3)
    edges_added = Tuple{Int,Int}[]
    
    for _ in 1:min(L.d, length(candidates))
        best_edge = nothing
        best_gap = -Inf
        
        for (u, v) in candidates
            v in get(L.adjacency, u, Set{Int}()) && continue
            
            preserves, _ = test_edge_preserves_ramanujan(L, u, v)
            if preserves
                add_edge!(L, u, v)
                gap = spectral_gap(L)
                remove_edge!(L, u, v)
                
                if gap > best_gap
                    best_gap = gap
                    best_edge = (u, v)
                end
            end
        end
        
        if !isnothing(best_edge)
            add_edge!(L, best_edge...)
            push!(edges_added, best_edge)
            filter!(c -> c != best_edge, candidates)
        end
    end
    
    push!(L.history, EdgeLearningStep(
        node_id, edges_added, gap_before, 
        spectral_gap(L), is_ramanujan(L)
    ))
    
    return node_id
end

function random_walk(L::SpectralEmbeddingLearner, steps::Int; 
                     start::Union{Int,Nothing}=nothing, teleport_prob::Float64=0.15)
    n_vertices(L) == 0 && return Int[]
    
    current = isnothing(start) ? rand(0:n_vertices(L)-1) : start
    path = [current]
    
    for _ in 1:steps
        if rand() < teleport_prob
            current = rand(0:n_vertices(L)-1)
        else
            neighbors = collect(get(L.adjacency, current, Set{Int}()))
            !isempty(neighbors) && (current = rand(neighbors))
        end
        push!(path, current)
    end
    
    return path
end

function walk_coverage(L::SpectralEmbeddingLearner, steps::Int; runs::Int=10)
    coverages = Float64[]
    for _ in 1:runs
        path = random_walk(L, steps)
        push!(coverages, length(unique(path)) / max(n_vertices(L), 1))
    end
    return sum(coverages) / length(coverages)
end

function gf3_trit(L::SpectralEmbeddingLearner)
    eff = gap_efficiency(L)
    eff >= 0.9 ? 0 : (eff >= 0.5 ? 1 : -1)
end

function gay_color(L::SpectralEmbeddingLearner)
    GayCompat.hex_at(L.seed, n_vertices(L))
end

function demo()
    println("=== Spectral Embedding Learner (Julia + Gay.jl) ===\n")
    
    learner = SpectralEmbeddingLearner(seed=1069, gamut_prime=3, target_degree=4)
    
    println("Seed: $(learner.seed)")
    println("Gamut prime: $(learner.p) (depth = log_$(learner.p)(n))")
    println("Target degree: $(learner.d)")
    println("Ramanujan bound: λ₂ ≤ $(round(ramanujan_bound(learner), digits=4))")
    println("Optimal gap: $(round(optimal_gap(learner), digits=4))\n")
    
    n_nodes = 20
    dim = 64
    
    println("Adding $n_nodes nodes with $dim-dim embeddings...\n")
    
    for i in 1:n_nodes
        emb = randn(dim)
        emb ./= norm(emb)
        add_node!(learner, emb)
        
        if i % 5 == 0
            m = metrics(learner)
            color = gay_color(learner)
            println("  n=$(lpad(i, 2)): gap=$(round(m.gap, digits=4)), " *
                    "λ₂=$(round(m.lambda_2, digits=4)), " *
                    "eff=$(round(m.gap_efficiency*100, digits=1))%, " *
                    "ramanujan=$(m.is_ramanujan), color=$color")
        end
    end
    
    println("\n=== Final Metrics ===")
    m = metrics(learner)
    println("Spectral gap: $(round(m.gap, digits=4))")
    println("λ₂: $(round(m.lambda_2, digits=4)) (bound: $(round(ramanujan_bound(learner), digits=4)))")
    println("Gap efficiency: $(round(m.gap_efficiency*100, digits=1))%")
    println("Is Ramanujan: $(m.is_ramanujan)")
    println("Mixing time: $(round(m.mixing_time, digits=2)) steps")
    println("GF(3) trit: $(gf3_trit(learner))")
    println("Gay color: $(gay_color(learner))")
    
    println("\n=== Random Walk Coverage ===")
    for steps in [10, 50, 100]
        coverage = walk_coverage(learner, steps, runs=20)
        println("  $(lpad(steps, 3)) steps: $(round(coverage*100, digits=1))% coverage")
    end
    
    println("\n=== GF(3) Conservation Check ===")
    total_trit = gf3_trit(learner)
    println("Learner trit: $total_trit (ERGODIC=0, optimal mixing)")
    
    return learner
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    demo()
end
