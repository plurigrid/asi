# Julia Performance Maximals: The Absurdly Performant Option

**Date**: 2025-12-22
**Insight**: Same seed → same output, but 100x faster
**Framework**: Gay.jl + OhMyThreads + LoopVectorization + StaticArrays

---

## The Performance Table: Always Choose Maximum

| Category | ❌ Standard | ✅ MAXIMALLY PERFORMANT | Speedup |
|----------|-------------|-------------------------|---------|
| **Threading** | `Threads.@threads` | `OhMyThreads.@tasks` / `Polyester.@batch` | **5x** |
| **SIMD Loops** | `@inbounds @fastmath for` | `@turbo for` (LoopVectorization) | **44x** |
| **Small Arrays** | `Vector{Float64}` | `SVector{N,Float64}` (StaticArrays) | **113x** |
| **Matrix Mult** | `A * B` | `@turbo` gemm or `Gaius.mul!` | **2x** MKL |
| **Reductions** | `sum(x)` | `vsum(x)` (LoopVectorization) | **1.4x** |
| **Allocations** | `Any[]` | `Vector{ConcreteType}` | **100x** |
| **RNG** | `rand()` | `SplitMix64` (deterministic) | **2x** |
| **Parallel Reduce** | `foldl` | `OhMyThreads.treduce` | **Nx** (cores) |
| **Broadcasting** | `A .* B` | `@turbo` broadcast | **5x** |
| **Type Stability** | `function f(x)` | `function f(x::T) where T` | **100x** |

---

## Category 1: Threading

### ❌ NEVER USE: `Threads.@threads`
```julia
# SLOW: High overhead, poor scheduling
@threads for i in 1:n
    result[i] = expensive(i)
end
```

### ✅ ALWAYS USE: `OhMyThreads.@tasks` or `Polyester.@batch`

```julia
using OhMyThreads

# Fast: Low overhead, work-stealing scheduler
tforeach(1:n) do i
    result[i] = expensive(i)
end

# Even faster for reductions
result = treduce(+, 1:n) do i
    compute(i)
end
```

**Benchmark**:
```
Threads.@threads: 417.282 ms
OhMyThreads.tforeach: 83.578 ms  ← 5x faster!
```

### ✅ For SIMD + Threads: `@tturbo`

```julia
using LoopVectorization

# SIMD + multithreading in one
@tturbo for i in 1:n
    result[i] = a[i] * b[i] + c[i]
end
```

---

## Category 2: SIMD Vectorization

### ❌ NEVER USE: Plain loops
```julia
function mygemm!(C, A, B)
    @inbounds @fastmath for m in axes(A,1), n in axes(B,2)
        Cmn = zero(eltype(C))
        for k in axes(A,2)
            Cmn += A[m,k] * B[k,n]
        end
        C[m,n] = Cmn
    end
end
# Time: 4.891 ms
```

### ✅ ALWAYS USE: `@turbo` from LoopVectorization

```julia
using LoopVectorization

function mygemmavx!(C, A, B)
    @turbo for m in axes(A,1), n in axes(B,2)
        Cmn = zero(eltype(C))
        for k in axes(A,2)
            Cmn += A[m,k] * B[k,n]
        end
        C[m,n] = Cmn
    end
end
# Time: 111.722 μs  ← 44x faster! Matches MKL BLAS!
```

**GFLOPs comparison** (191×189×171 matmul):
```
@inbounds @fastmath: 2.5 GFlops
@turbo:              110.5 GFlops  ← BLAS-competitive!
MKL BLAS:            105.3 GFlops
```

---

## Category 3: Small Fixed-Size Arrays

### ❌ NEVER USE: Heap-allocated arrays for small data
```julia
position = [1.0, 0.0, 0.0]  # Heap allocation, slow
```

### ✅ ALWAYS USE: `StaticArrays.SVector`

```julia
using StaticArrays

position = SA[1.0, 0.0, 0.0]  # Stack allocation, SIMD-friendly
```

**3×3 Matrix Benchmarks**:
```
Operation                          Speedup
─────────────────────────────────────────
Matrix determinant                 113x
Matrix inverse                     68x
Matrix QR decomposition            65x
Matrix addition                    33x
Symmetric eigendecomposition       25x
Cholesky decomposition             9x
LU decomposition                   6x
Matrix multiplication              6x
```

### ✅ For ODE solving with StaticArrays

```julia
using DifferentialEquations, StaticArrays

function lorenz_static(u, p, t)
    σ, ρ, β = p
    SA[σ*(u[2]-u[1]), u[1]*(ρ-u[3])-u[2], u[1]*u[2]-β*u[3]]
end

u0 = SA[1.0, 0.0, 0.0]
prob = ODEProblem(lorenz_static, u0, (0.0, 100.0))
# 10x faster than Vector version!
```

---

## Category 4: Type Stability

### ❌ NEVER USE: Type-unstable containers
```julia
function fslow(n)
    xs = []  # Any[] - type unstable!
    push!(xs, Ref(0))
    s = 0
    for i in 1:n
        xs[end][] = i
        s += xs[end][]
    end
    return s
end
# 432.200 μs (28950 allocations)
```

### ✅ ALWAYS USE: Concrete types

```julia
function ffast(n)
    xs = Base.RefValue{Int}[]  # Concrete type!
    push!(xs, Ref(0))
    s = 0
    for i in 1:n
        xs[end][] = i
        s += xs[end][]
    end
    return s
end
# 4.371 μs (3 allocations)  ← 100x faster!
```

---

## Category 5: Memory & Allocations

### ❌ NEVER: Allocate in hot loops
```julia
function bad()
    for i in 1:1000000
        v = [i, i+1, i+2]  # Allocates every iteration!
        process(v)
    end
end
```

### ✅ ALWAYS: Pre-allocate or use StaticArrays

```julia
function good()
    v = zeros(3)  # Pre-allocate once
    for i in 1:1000000
        v[1] = i; v[2] = i+1; v[3] = i+2
        process(v)
    end
end

# Or even better with StaticArrays:
function best()
    for i in 1:1000000
        v = SA[i, i+1, i+2]  # Stack allocation, free!
        process(v)
    end
end
```

---

## Category 6: SplitMix64 for Gay.jl Colors

### ✅ MAXIMALLY PERFORMANT SplitMix64

```julia
# lib/splitmix64_simd.jl
module SplitMix64SIMD

using LoopVectorization

const GOLDEN = 0x9E3779B97F4A7C15
const MIX1 = 0xBF58476D1CE4E5B9
const MIX2 = 0x94D049BB133111EB

struct SplitMix64
    state::UInt64
end

@inline function next!(rng::SplitMix64)
    z = rng.state + GOLDEN
    z = (z ⊻ (z >> 30)) * MIX1
    z = (z ⊻ (z >> 27)) * MIX2
    z ⊻ (z >> 31)
end

# SIMD batch generation for maximum throughput
function generate_colors_batch!(colors::Matrix{Float64}, seeds::Vector{UInt64})
    n = length(seeds)
    @turbo for i in 1:n
        z = seeds[i] + GOLDEN
        z = (z ⊻ (z >> 30)) * MIX1
        z = (z ⊻ (z >> 27)) * MIX2
        z = z ⊻ (z >> 31)
        
        # L channel
        z2 = z + GOLDEN
        z2 = (z2 ⊻ (z2 >> 30)) * MIX1
        z2 = (z2 ⊻ (z2 >> 27)) * MIX2
        z2 = z2 ⊻ (z2 >> 31)
        colors[1, i] = 10.0 + (z2 / typemax(UInt64)) * 85.0
        
        # C channel
        z3 = z2 + GOLDEN
        z3 = (z3 ⊻ (z3 >> 30)) * MIX1
        z3 = (z3 ⊻ (z3 >> 27)) * MIX2
        z3 = z3 ⊻ (z3 >> 31)
        colors[2, i] = (z3 / typemax(UInt64)) * 100.0
        
        # H channel
        z4 = z3 + GOLDEN
        z4 = (z4 ⊻ (z4 >> 30)) * MIX1
        z4 = (z4 ⊻ (z4 >> 27)) * MIX2
        z4 = z4 ⊻ (z4 >> 31)
        colors[3, i] = (z4 / typemax(UInt64)) * 360.0
    end
end

# GF(3) trit computation
@inline function hue_to_trit(h::Float64)::Int8
    h < 60.0 || h >= 300.0 ? Int8(1) :
    h < 180.0 ? Int8(0) : Int8(-1)
end

# Batch trit computation with SIMD
function compute_trits!(trits::Vector{Int8}, hues::Vector{Float64})
    n = length(hues)
    @turbo for i in 1:n
        h = hues[i]
        trits[i] = h < 60.0 || h >= 300.0 ? Int8(1) :
                   h < 180.0 ? Int8(0) : Int8(-1)
    end
end

end # module
```

---

## Category 7: Parallel Reductions

### ❌ NEVER: Sequential reduce
```julia
result = foldl(+, 1:10_000_000)  # Single-threaded
```

### ✅ ALWAYS: `OhMyThreads.treduce`

```julia
using OhMyThreads

result = treduce(+, 1:10_000_000)  # Parallel!
# Or with custom operation:
result = treduce(1:10_000_000; init=0.0) do i
    sin(Float64(i))
end
```

---

## The Gay.jl Performance Stack

```
┌─────────────────────────────────────────────────────────────────┐
│  Gay.jl Color Generation (Deterministic SplitMix64)            │
├─────────────────────────────────────────────────────────────────┤
│  @turbo (LoopVectorization) for SIMD color batches             │
├─────────────────────────────────────────────────────────────────┤
│  StaticArrays.SVector{3,Float64} for LCH colors                │
├─────────────────────────────────────────────────────────────────┤
│  OhMyThreads.tforeach for parallel skill execution             │
├─────────────────────────────────────────────────────────────────┤
│  ACSets with indexed parts for O(1) lookups                    │
├─────────────────────────────────────────────────────────────────┤
│  GF(3) conservation: trit sum ≡ 0 (mod 3) per triplet          │
└─────────────────────────────────────────────────────────────────┘
```

---

## Package Recommendations Summary

| Use Case | Package | Why |
|----------|---------|-----|
| Threading | **OhMyThreads.jl** | Work-stealing, composable, low overhead |
| SIMD | **LoopVectorization.jl** | Auto-vectorization, BLAS-competitive |
| Small Arrays | **StaticArrays.jl** | Stack allocation, type-stable size |
| ACSet Data | **ACSets.jl** | Categorical databases, indexed queries |
| Parallel Sort | **ThreadsX.jl** | Parallel `sort!`, `map`, `reduce` |
| GPU | **CUDA.jl** / **Metal.jl** | NVIDIA / Apple Silicon |
| Tensor Ops | **Tullio.jl** | Einstein notation + LoopVectorization |
| Profiling | **Profile.@profile** | Per-thread profiling in Julia 1.8+ |
| **Verified** | **IntervalArithmetic.jl** | **Guaranteed bounds** (EU Maximalism) |

---

## EU Maximalism: Fixing the World with the Right Numbers

> *"If your computation isn't verified, it's just expensive guessing."*

### The IntervalArithmetic.jl Guarantee

[IntervalArithmetic.jl](https://github.com/JuliaIntervals/IntervalArithmetic.jl) implements **validated numerics** — computations with mathematically guaranteed bounds. No more floating-point surprises.

### ❌ Dangerous Float (American Optimism)
```julia
# "It's probably fine"
x = 0.1 + 0.2
x == 0.3  # false! 😱
# x = 0.30000000000000004
```

### ✅ Guaranteed Interval (EU Maximalism)
```julia
using IntervalArithmetic

# "I DEMAND mathematical certainty"
x = interval(0.1) + interval(0.2)
# Interval{Float64}(0.29999999999999998, 0.30000000000000004)

in_interval(0.3, x)  # true ✓ (0.3 is definitely in there)
```

### Core Philosophy

```
AMERICAN APPROACH          EU MAXIMALIST APPROACH
─────────────────          ─────────────────────
"Move fast"                "Move correctly"
Float64                    Interval{Float64}
"Approximately π"          "Definitely contains π"
Hope for the best          Guarantee the bounds
Ship it!                   Verify it first
```

### Interval Arithmetic Operations

```julia
using IntervalArithmetic, IntervalArithmetic.Symbols

# Elegant notation with Symbols
a = 0 .. 2          # [0, 2]
b = 1 ± 0.5         # [0.5, 1.5]

# Containment checks
b ⊑ a               # b ⊆ a? true
∅ ⪽ ℝ               # empty ⊊ reals

# Rigorous π computation
pi_interval = interval(BigFloat, π)
in_interval(π, pi_interval)  # true, mathematically guaranteed
```

### Root Finding with Guarantees

```julia
using IntervalArithmetic, IntervalRootFinding

f(x) = sin(x) - 0.1*x^2 + 1

# Returns intervals GUARANTEED to contain roots
roots(f, -10..10)
# 4-element Vector{Root{Interval{Float64}}}:
#  Root([3.14959, 3.1496], :unique)     ← root definitely in here
#  Root([-4.42654, -4.42653], :unique)
#  Root([-3.10682, -3.10681], :unique)
#  Root([-1.08205, -1.08204], :unique)
```

### Linear Algebra with Bounds

```julia
using IntervalArithmetic, IntervalLinearAlgebra

A = [interval(1, 1.1)  interval(2, 2.1);
     interval(3, 3.1)  interval(4, 4.1)]

# Rigorous matrix inverse with guaranteed bounds
inv(A)
# 2×2 Matrix{Interval{Float64}}:
#  [-4.2, -3.7]   [1.9, 2.2]
#  [2.8, 3.2]     [-1.1, -0.9]
```

### GF(3) Triad for Verified Computing

```
# EU Maximalist Triad
interval-validate (-1) ⊗ interval-compute (0) ⊗ interval-output (+1) = 0 ✓

Breakdown:
  interval-validate (-1)  : Check inputs are valid intervals
  interval-compute (0)    : Perform verified arithmetic
  interval-output (+1)    : Produce guaranteed result bounds
```

### Performance + Correctness

You can have both! Combine with `@turbo`:

```julia
using IntervalArithmetic, LoopVectorization

function verified_sum(x::Vector{Interval{Float64}})
    s = interval(0.0)
    @inbounds for i in eachindex(x)  # Can't use @turbo with intervals yet
        s += x[i]
    end
    s
end

# Result: Interval guaranteed to contain true sum
```

### JuliaIntervals Ecosystem

| Package | Purpose |
|---------|---------|
| **IntervalArithmetic.jl** | Core interval types & operations |
| **IntervalRootFinding.jl** | Find ALL roots with proofs |
| **IntervalLinearAlgebra.jl** | Verified linear algebra |
| **IntervalConstraintProgramming.jl** | Constraint satisfaction |
| **IntervalOptimisation.jl** | Global optimization with guarantees |
| **TaylorModels.jl** | Validated ODE solving |

### When to Use Verified Computing

| Scenario | Float64 | Interval |
|----------|---------|----------|
| Game physics | ✓ | |
| ML training | ✓ | |
| Financial regulations | | ✓ |
| Safety-critical systems | | ✓ |
| Scientific claims | | ✓ |
| Theorem proving | | ✓ |
| "Did my ODE solver converge?" | | ✓ |

### The EU Maximalist Manifesto

1. **Every computation has error bounds** — know them
2. **Floating-point is approximate** — intervals are rigorous  
3. **Trust but verify** — mathematically prove your results
4. **Correctness before speed** — but also: correctness WITH speed
5. **The right number** — is an interval containing the truth

---

## GF(3) Balanced Skill Triads for Performance

```
# Core Performance Triad
loopvectorization (-1, validator) ⊗ ohmythreads (0, coordinator) ⊗ staticarrays (+1, generator) = 0 ✓

# ACSet Performance Triad  
acsets-index (-1) ⊗ catlab-compose (0) ⊗ algebraicdynamics (+1) = 0 ✓

# Gay.jl Color Triad
splitmix-validate (-1) ⊗ gay-generate (0) ⊗ color-batch (+1) = 0 ✓
```

---

## Benchmarking Commands

```bash
# Run Julia performance tests
just julia-perf-threading      # Compare threading approaches
just julia-perf-simd           # Compare SIMD approaches
just julia-perf-staticarrays   # Compare array types
just julia-perf-splitmix       # Benchmark color generation

# Full performance suite
just julia-perf-all
```

---

## References

1. [OhMyThreads.jl](https://github.com/JuliaFolds2/OhMyThreads.jl) - Simple multithreading
2. [LoopVectorization.jl](https://github.com/JuliaSIMD/LoopVectorization.jl) - SIMD magic
3. [StaticArrays.jl](https://github.com/JuliaArrays/StaticArrays.jl) - Stack-allocated arrays
4. [Polyester.jl](https://github.com/JuliaSIMD/Polyester.jl) - Cheapest threads
5. [ACSets.jl](https://github.com/AlgebraicJulia/ACSets.jl) - Categorical databases
6. [Julia Performance Tips](https://docs.julialang.org/en/v1/manual/performance-tips/)

---

**The Golden Rule**: 
> *Same seed → same output. But 100x faster.*

Every skill in the entropy world uses:
- `@turbo` for loops
- `SVector` for small data
- `OhMyThreads` for parallelism
- Deterministic `SplitMix64` for reproducibility
