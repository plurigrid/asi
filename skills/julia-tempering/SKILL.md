---
metadata:
  interface_ports:
  - References
---
# Julia-Tempering Skill

Splittable RNG infrastructure for parallel tempering and distributed sampling with deterministic reproducibility.

## Core Packages

### SplittableRandoms.jl
```julia
using SplittableRandoms

# Create deterministic splittable RNG
rng = SplittableRandom(seed)

# Split into independent streams (deterministic!)
rng_a, rng_b = split(rng, 2)

# N-way split for parallel workers
rngs = split(rng, n_workers)

# Each stream is independent but reproducible
@assert rand(split(SplittableRandom(42), 2)[1]) == rand(split(SplittableRandom(42), 2)[1])
```

### Pigeons.jl Parallel Tempering
```julia
using Pigeons

# Parallel tempering with splittable RNG
pt = pigeons(
    target = target_distribution,
    n_rounds = 10,
    n_chains = 8,
    seed = 12345  # Deterministic across runs
)

# Distributed execution preserves reproducibility
pt_distributed = pigeons(
    target = target,
    on = ChildProcess(n_local_mpi_processes = 4),
    seed = 12345
)

# Strong Parallelism Invariance: same results regardless of parallelism
@assert pt.reduced_recorders == pt_distributed.reduced_recorders
```

## Gay.jl Integration

Deterministic color generation from splittable RNG streams:

```julia
using SplittableRandoms
using Gay  # Gay.jl color generation

# Seed from SplittableRandom state
function gay_from_splittable(rng::SplittableRandom)
    # Extract deterministic value for Gay.jl seed
    seed_val = rand(rng, UInt64)
    gay_seed!(seed_val)
    next_color()
end

# Parallel color streams via split
rng = SplittableRandom(42)
color_rngs = split(rng, 3)
colors = [gay_from_splittable(r) for r in color_rngs]

# Same seed → same colors, always
@assert colors == let rng2 = SplittableRandom(42)
    [gay_from_splittable(r) for r in split(rng2, 3)]
end
```

## Strong Parallelism Invariance (SPI)

SPI guarantees identical results regardless of execution topology:

```julia
# SPI Property: f(split(rng, n)) produces same result for any n partitioning
function verify_spi(seed, computation)
    rng = SplittableRandom(seed)
    
    # Serial execution
    serial_result = computation(split(rng, 1)[1])
    
    # Parallel execution (2-way)
    rng2 = SplittableRandom(seed)
    parallel_2 = merge_results([computation(r) for r in split(rng2, 2)])
    
    # Parallel execution (4-way)
    rng4 = SplittableRandom(seed)
    parallel_4 = merge_results([computation(r) for r in split(rng4, 4)])
    
    @assert serial_result == parallel_2 == parallel_4
end
```

### SPI for Tempering
```julia
using Pigeons

# Round-trip invariant: swap acceptance independent of worker count
function spi_tempering_test(seed)
    target = toy_mvn_target(2)
    
    results_1 = pigeons(target=target, n_chains=4, seed=seed, on=ChildProcess(1))
    results_4 = pigeons(target=target, n_chains=4, seed=seed, on=ChildProcess(4))
    
    # Swap statistics must match
    @assert results_1.shared.swap_stats == results_4.shared.swap_stats
end
```

## MaxEnt Triad Testing Protocol

Three agents maximize mutual information through complementary verification:

| Agent | Role | Verifies |
|-------|------|----------|
| julia-gpu-kernels | RNG consumer | Kernel uses SplittableRandom |
| enzyme-autodiff | Gradient checker | Differentiates RNG-based loss |
| julia-tempering | RNG provider | split() preserves determinism |

### Test: Splittable RNG for Parallel Computation
```julia
using SplittableRandoms

rng = SplittableRandom(12345)
rng_a, rng_b = split(rng, 2)

# Same seed → same split → same values
@assert rand(rng_a) == rand(SplittableRandom(12345) |> x -> split(x, 2)[1])
```

### Test: GPU Kernel RNG (Agent A: julia-gpu-kernels)
```julia
using CUDA, SplittableRandoms

function kernel_with_rng!(out, rng_states)
    i = threadIdx().x
    # Each thread gets deterministic stream
    local_rng = rng_states[i]
    out[i] = rand(local_rng)
    return
end

# Agent A verifies: GPU kernel produces deterministic output
seed = 42
rngs = split(SplittableRandom(seed), 256)
@cuda threads=256 kernel_with_rng!(out, rngs)

# Reproducibility check
rngs2 = split(SplittableRandom(seed), 256)
@cuda threads=256 kernel_with_rng!(out2, rngs2)
@assert out == out2  # SPI holds on GPU
```

### Test: Differentiable RNG (Agent B: enzyme-autodiff)
```julia
using Enzyme, SplittableRandoms

function stochastic_loss(params, rng)
    # RNG-dependent computation
    noise = rand(rng) * 0.1
    return sum(params.^2) + noise
end

# Agent B verifies: Enzyme differentiates through RNG correctly
seed = 12345
rng = SplittableRandom(seed)
params = [1.0, 2.0, 3.0]

grad = Enzyme.gradient(Enzyme.Reverse, p -> stochastic_loss(p, rng), params)

# Gradient reproducible with same seed
rng2 = SplittableRandom(seed)
grad2 = Enzyme.gradient(Enzyme.Reverse, p -> stochastic_loss(p, rng2), params)
@assert grad == grad2
```

### Test: Provider Infrastructure (Agent C: julia-tempering)
```julia
using SplittableRandoms, Pigeons

# Agent C provides RNG infrastructure for A and B
function provide_rng_infrastructure(seed, n_consumers)
    master_rng = SplittableRandom(seed)
    
    # Deterministic allocation to consumers
    consumer_rngs = split(master_rng, n_consumers)
    
    # Each consumer gets independent, reproducible stream
    return consumer_rngs
end

# Verification: infrastructure preserves SPI
rngs_run1 = provide_rng_infrastructure(42, 3)
rngs_run2 = provide_rng_infrastructure(42, 3)

for (r1, r2) in zip(rngs_run1, rngs_run2)
    @assert rand(r1) == rand(r2)
end
```

### Triad Integration Test
```julia
# Full pipeline: tempering → GPU → autodiff
function triad_integration_test(seed)
    using SplittableRandoms, Pigeons, CUDA, Enzyme
    
    # Agent C: Provide infrastructure
    master = SplittableRandom(seed)
    rng_gpu, rng_autodiff, rng_tempering = split(master, 3)
    
    # Agent A: GPU computation
    gpu_result = cuda_monte_carlo(rng_gpu, 1000)
    
    # Agent B: Differentiate
    gradient = enzyme_gradient(rng_autodiff, gpu_result)
    
    # Agent C: Parallel tempering refinement
    refined = pigeons(
        target = make_target(gradient),
        seed = rand(rng_tempering, UInt64)
    )
    
    return refined
end

# SPI: Results identical across runs
@assert triad_integration_test(42) == triad_integration_test(42)
```

## Key Invariants

1. **Determinism**: `split(SplittableRandom(s), n)` always produces same streams
2. **Independence**: Split streams have no statistical correlation
3. **SPI**: Computation result independent of parallelism degree
4. **Composability**: Splits can be further split maintaining all properties

---

## End-of-Skill Interface

## References

- [SplittableRandoms.jl](https://github.com/JuliaRandom/SplittableRandoms.jl)
- [Pigeons.jl](https://pigeons.run/)
- [Gay.jl](https://github.com/bmorphism/Gay.jl)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*


## REPL atlas

Part of: `repl-commons`. Family canonical: `sicm`.
