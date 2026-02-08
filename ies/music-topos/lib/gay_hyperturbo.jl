#!/usr/bin/env julia
# lib/gay_hyperturbo.jl
#
# HYPERTURBO: Maximum Performance Gay.jl Color Generation
# Combines: Polyester + SIMD.jl + OhMyThreads + Manual Vectorization
#
# Target: 1B+ colors/sec on Apple Silicon

module GayHyperturbo

using SIMD
using Polyester
using StaticArrays

export generate_colors_hyper!, benchmark_all

# =============================================================================
# SplitMix64 Constants
# =============================================================================

const GOLDEN = 0x9E3779B97F4A7C15
const MIX1 = 0xBF58476D1CE4E5B9
const MIX2 = 0x94D049BB133111EB
const MASK64 = 0xFFFFFFFFFFFFFFFF
const INV_MASK = 1.0 / Float64(MASK64)

# =============================================================================
# SIMD SplitMix64 (4-wide for AVX2, 8-wide for AVX-512)
# =============================================================================

const LANES = 4  # Use 4 for portable SIMD

const GOLDEN_VEC = Vec{LANES, UInt64}((GOLDEN, GOLDEN, GOLDEN, GOLDEN))
const MIX1_VEC = Vec{LANES, UInt64}((MIX1, MIX1, MIX1, MIX1))
const MIX2_VEC = Vec{LANES, UInt64}((MIX2, MIX2, MIX2, MIX2))

@inline function splitmix_simd(seeds::Vec{LANES, UInt64})
    z = seeds + GOLDEN_VEC
    z = (z ⊻ (z >> 30)) * MIX1_VEC
    z = (z ⊻ (z >> 27)) * MIX2_VEC
    z ⊻ (z >> 31)
end

@inline function splitmix_next(z::Vec{LANES, UInt64})
    z = z + GOLDEN_VEC
    z = (z ⊻ (z >> 30)) * MIX1_VEC
    z = (z ⊻ (z >> 27)) * MIX2_VEC
    z ⊻ (z >> 31)
end

@inline function u64_to_f64(v::Vec{LANES, UInt64})
    # Convert UInt64 to Float64 element-wise
    Vec{LANES, Float64}((
        Float64(v[1]),
        Float64(v[2]),
        Float64(v[3]),
        Float64(v[4])
    ))
end

# =============================================================================
# Batch Data Structure (SoA for cache efficiency)
# =============================================================================

struct ColorBatchHyper
    L::Vector{Float64}
    C::Vector{Float64}
    H::Vector{Float64}
    trits::Vector{Int8}
    n::Int
end

function ColorBatchHyper(n::Int)
    # Pad to LANES boundary for SIMD
    padded = ((n + LANES - 1) ÷ LANES) * LANES
    ColorBatchHyper(
        Vector{Float64}(undef, padded),
        Vector{Float64}(undef, padded),
        Vector{Float64}(undef, padded),
        Vector{Int8}(undef, padded),
        n
    )
end

# =============================================================================
# Method 1: Explicit SIMD.jl Vectorization
# =============================================================================

function generate_colors_simd!(batch::ColorBatchHyper, base_seed::UInt64)
    n = length(batch.L)
    L = batch.L
    C = batch.C
    H = batch.H
    trits = batch.trits
    
    @inbounds for i in 1:LANES:n
        # Load 4 consecutive seeds
        seeds = Vec{LANES, UInt64}((
            base_seed + UInt64(i - 1),
            base_seed + UInt64(i),
            base_seed + UInt64(i + 1),
            base_seed + UInt64(i + 2)
        ))
        
        # Generate L values
        z = splitmix_simd(seeds)
        l_vec = 10.0 + u64_to_f64(z) * (INV_MASK * 85.0)
        
        # Generate C values
        z = splitmix_next(z)
        c_vec = u64_to_f64(z) * (INV_MASK * 100.0)
        
        # Generate H values
        z = splitmix_next(z)
        h_vec = u64_to_f64(z) * (INV_MASK * 360.0)
        
        # Store results
        vstore(l_vec, pointer(L, i))
        vstore(c_vec, pointer(C, i))
        vstore(h_vec, pointer(H, i))
    end
    
    # Compute trits (scalar, fast enough)
    @inbounds @simd for i in 1:n
        h = H[i]
        trits[i] = (h < 60.0 || h >= 300.0) ? Int8(1) : (h < 180.0) ? Int8(0) : Int8(-1)
    end
    
    batch
end

# =============================================================================
# Method 2: Polyester @batch (Cheapest Threads)
# =============================================================================

function generate_colors_polyester!(batch::ColorBatchHyper, base_seed::UInt64)
    n = batch.n
    L = batch.L
    C = batch.C
    H = batch.H
    trits = batch.trits
    
    @batch per=core for i in 1:n
        seed = base_seed + UInt64(i - 1)
        
        # SplitMix64 step 1
        z = seed + GOLDEN
        z = (z ⊻ (z >> 30)) * MIX1
        z = (z ⊻ (z >> 27)) * MIX2
        z = z ⊻ (z >> 31)
        L[i] = 10.0 + Float64(z) * INV_MASK * 85.0
        
        # SplitMix64 step 2
        z = z + GOLDEN
        z = (z ⊻ (z >> 30)) * MIX1
        z = (z ⊻ (z >> 27)) * MIX2
        z = z ⊻ (z >> 31)
        C[i] = Float64(z) * INV_MASK * 100.0
        
        # SplitMix64 step 3
        z = z + GOLDEN
        z = (z ⊻ (z >> 30)) * MIX1
        z = (z ⊻ (z >> 27)) * MIX2
        z = z ⊻ (z >> 31)
        h = Float64(z) * INV_MASK * 360.0
        H[i] = h
        
        trits[i] = (h < 60.0 || h >= 300.0) ? Int8(1) : (h < 180.0) ? Int8(0) : Int8(-1)
    end
    
    batch
end

# =============================================================================
# Method 3: Hybrid SIMD + Polyester
# =============================================================================

function generate_colors_hybrid!(batch::ColorBatchHyper, base_seed::UInt64)
    n = length(batch.L)
    L = batch.L
    C = batch.C
    H = batch.H
    trits = batch.trits
    
    chunk_size = n ÷ Threads.nthreads()
    chunk_size = ((chunk_size + LANES - 1) ÷ LANES) * LANES  # Align to LANES
    
    @batch per=core for tid in 1:Threads.nthreads()
        start_idx = (tid - 1) * chunk_size + 1
        end_idx = min(tid * chunk_size, n)
        
        @inbounds for i in start_idx:LANES:end_idx
            seeds = Vec{LANES, UInt64}((
                base_seed + UInt64(i - 1),
                base_seed + UInt64(i),
                base_seed + UInt64(i + 1),
                base_seed + UInt64(i + 2)
            ))
            
            z = splitmix_simd(seeds)
            l_vec = 10.0 + u64_to_f64(z) * (INV_MASK * 85.0)
            
            z = splitmix_next(z)
            c_vec = u64_to_f64(z) * (INV_MASK * 100.0)
            
            z = splitmix_next(z)
            h_vec = u64_to_f64(z) * (INV_MASK * 360.0)
            
            vstore(l_vec, pointer(L, i))
            vstore(c_vec, pointer(C, i))
            vstore(h_vec, pointer(H, i))
        end
    end
    
    @inbounds @simd for i in 1:batch.n
        h = H[i]
        trits[i] = (h < 60.0 || h >= 300.0) ? Int8(1) : (h < 180.0) ? Int8(0) : Int8(-1)
    end
    
    batch
end

# =============================================================================
# Method 4: Unrolled Scalar (Baseline Comparison)
# =============================================================================

function generate_colors_scalar!(batch::ColorBatchHyper, base_seed::UInt64)
    n = batch.n
    L = batch.L
    C = batch.C
    H = batch.H
    trits = batch.trits
    
    @inbounds for i in 1:n
        seed = base_seed + UInt64(i - 1)
        
        z = seed + GOLDEN
        z = (z ⊻ (z >> 30)) * MIX1
        z = (z ⊻ (z >> 27)) * MIX2
        z = z ⊻ (z >> 31)
        L[i] = 10.0 + Float64(z) * INV_MASK * 85.0
        
        z = z + GOLDEN
        z = (z ⊻ (z >> 30)) * MIX1
        z = (z ⊻ (z >> 27)) * MIX2
        z = z ⊻ (z >> 31)
        C[i] = Float64(z) * INV_MASK * 100.0
        
        z = z + GOLDEN
        z = (z ⊻ (z >> 30)) * MIX1
        z = (z ⊻ (z >> 27)) * MIX2
        z = z ⊻ (z >> 31)
        h = Float64(z) * INV_MASK * 360.0
        H[i] = h
        
        trits[i] = (h < 60.0 || h >= 300.0) ? Int8(1) : (h < 180.0) ? Int8(0) : Int8(-1)
    end
    
    batch
end

# =============================================================================
# Benchmark Suite
# =============================================================================

function benchmark_method(name::String, fn::Function, batch::ColorBatchHyper, seed::UInt64; runs=5)
    # Warmup
    fn(batch, seed)
    
    times = Float64[]
    for _ in 1:runs
        t0 = time_ns()
        fn(batch, seed)
        t1 = time_ns()
        push!(times, (t1 - t0) / 1e6)
    end
    
    min_time = minimum(times)
    throughput = batch.n / (min_time / 1000) / 1e9
    
    println("  $name: $(round(min_time, digits=3)) ms → $(round(throughput, digits=2)) B/s")
    throughput
end

function benchmark_all()
    println("╔═══════════════════════════════════════════════════════════════════╗")
    println("║  Gay.jl HYPERTURBO - Maximum Performance Benchmark               ║")
    println("╚═══════════════════════════════════════════════════════════════════╝")
    println()
    println("Threads: $(Threads.nthreads())")
    println("SIMD lanes: $LANES")
    println()
    
    for n in [1_000_000, 10_000_000, 100_000_000]
        println("─── N = $(n ÷ 1_000_000)M colors ───")
        batch = ColorBatchHyper(n)
        seed = UInt64(0x42D)
        
        results = Dict{String, Float64}()
        
        results["Scalar"] = benchmark_method("Scalar    ", generate_colors_scalar!, batch, seed)
        results["SIMD"] = benchmark_method("SIMD.jl   ", generate_colors_simd!, batch, seed)
        results["Polyester"] = benchmark_method("Polyester ", generate_colors_polyester!, batch, seed)
        results["Hybrid"] = benchmark_method("Hybrid    ", generate_colors_hybrid!, batch, seed)
        
        best = maximum(values(results))
        winner = [k for (k,v) in results if v == best][1]
        println("  Winner: $winner ($(round(best, digits=2)) B colors/sec)")
        println()
    end
end

function demo()
    println("─── Quick Demo ───")
    batch = ColorBatchHyper(12)
    generate_colors_hybrid!(batch, UInt64(0x42D))
    
    println("First 6 colors:")
    for i in 1:6
        trit_char = batch.trits[i] == 1 ? "+" : (batch.trits[i] == -1 ? "-" : "0")
        println("  [$trit_char] L=$(round(batch.L[i], digits=1)) C=$(round(batch.C[i], digits=1)) H=$(round(batch.H[i], digits=1))°")
    end
    println()
end

end # module

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    using .GayHyperturbo
    GayHyperturbo.demo()
    GayHyperturbo.benchmark_all()
end
