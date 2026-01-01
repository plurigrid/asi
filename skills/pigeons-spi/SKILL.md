---
metadata:
  interface_ports:
  - References
  - Commands
---
# pigeons-spi Skill

```yaml
name: pigeons-spi
description: Pigeons.jl parallel tempering MCMC with Strong Parallelism Invariance (SPI) via SplittableRandoms
version: 1.0.0
trit: +1  # PLUS - generates samples, produces output
```

## Overview

Pigeons.jl implements **Strong Parallelism Invariance (SPI)**: identical results regardless of number of parallel workers. This is the pattern Gay.jl adopts for deterministic color generation.

**Key Insight**: `same seed → same samples → same colors`

## SPI Pattern: SplittableRandoms

The core innovation: determinism via splittable random streams.

```julia
using Pigeons
using SplittableRandoms

# SPI: same seed produces identical results on 1, 4, or 100 workers
rng = SplittableRandom(1069)  # Our seed from AGENTS.md

# Split creates independent streams with deterministic relationship
rng1, rng2 = split(rng)
rng_a, rng_b, rng_c = split(rng1, 3)  # 3-way split for GF(3) triads
```

## Parallel Tempering

```julia
using Pigeons

# Basic parallel tempering
pt = pigeons(
    target = my_target,
    n_chains = 10,        # Number of temperature chains
    n_rounds = 12,        # 2^12 = 4096 samples per chain
    seed = 1069,          # SPI: reproducible across workers
    explorer = SliceSampler()  # or AutoMALA()
)

# Get samples
samples = Chains(pt)
```

### Explorers

| Explorer | Use Case |
|----------|----------|
| `SliceSampler()` | General purpose, robust |
| `AutoMALA()` | High-dimensional, auto-tuned HMC |
| `Mix(SliceSampler(), AutoMALA())` | Combine strategies |

## Target Interface

```julia
using LogDensityProblems

struct MyTarget
    dim::Int
    data::Vector{Float64}
end

# Required interface
LogDensityProblems.dimension(t::MyTarget) = t.dim
LogDensityProblems.logdensity(t::MyTarget, x) = -sum((x .- t.data).^2) / 2

# Optional: better initialization
Pigeons.initialization(t::MyTarget, rng, _) = randn(rng, t.dim)

# Optional: extract samples
Pigeons.extract_sample(state, _) = copy(state.x)
```

## Gay.jl Connection

Both packages share the SplittableRandoms pattern:

```julia
using Gay
using Pigeons
using SplittableRandoms

# Same seed, deterministic across both packages
seed = 1069
Gay.seed!(seed)

# Pigeons MCMC with colored diagnostics
pt = pigeons(target = my_target, seed = seed, n_rounds = 10)

# Color each chain with Gay.jl
for (i, chain) in enumerate(1:pt.n_chains)
    hex = Gay.color_at(seed, i)
    trit = Gay.trit_at(seed, i)  # GF(3): -1, 0, +1
    println("Chain $i: $hex (trit=$trit)")
end

# GF(3) conservation: sum of trits ≡ 0 (mod 3)
```

### Colored Diagnostics

```julia
function colored_pt_summary(pt, seed)
    println("Parallel Tempering with Gay.jl Colors")
    println("=" ^ 40)
    
    for round in 1:pt.n_rounds
        hex = Gay.color_at(seed, round)
        logZ = stepping_stone(pt, round)
        println("Round $round: $hex | log(Z) ≈ $(round(logZ, digits=3))")
    end
end
```

## Comrade.jl Integration

Comrade uses Pigeons for Event Horizon Telescope black hole imaging:

```julia
using Comrade
using Pigeons

# Black hole image model
model = ComradeModel(data, prior)

# Run parallel tempering MCMC
chain = sample(model, Pigeons.PT(
    n_chains = 16,
    n_rounds = 14,
    explorer = AutoMALA()
), seed = 1069)

# Posterior images with deterministic colors
for (i, img) in enumerate(posterior_images(chain))
    color = Gay.color_at(1069, i)
    # Apply color to visualization
end
```

## GF(3) Triadic Pattern

Pigeons.jl as PLUS (+1) in the triad:

| Trit | Role | Package |
|------|------|---------|
| -1 (MINUS) | Consumes/validates | DynamicPPL priors |
| 0 (ERGODIC) | Coordinates | Pigeons controller |
| +1 (PLUS) | Generates output | Pigeons samples |

```julia
# Conservation: samples generated (PLUS) must balance constraints (MINUS)
n_samples = 2^12
n_constraints = length(prior_bounds)
@assert mod(n_samples - n_constraints + 0, 3) == 0  # GF(3) conserved
```

---

## End-of-Skill Interface

## Commands

```bash
# Install
julia -e 'using Pkg; Pkg.add("Pigeons")'

# Run with colored output
julia --project=@Gay -e '
using Pigeons, Gay
Gay.seed!(1069)
pt = pigeons(target = toy_mvn_target(3), n_rounds = 8, seed = 1069)
for i in 1:8
    println("Round $i: $(Gay.color_at(1069, i))")
end
'

# Verify SPI (same results on different worker counts)
julia -p 4 -e '
using Pigeons
pt1 = pigeons(target = toy_mvn_target(3), seed = 42, n_workers = 1)
pt4 = pigeons(target = toy_mvn_target(3), seed = 42, n_workers = 4)
@assert stepping_stone(pt1) ≈ stepping_stone(pt4)  # SPI verified
'
```

## References

- [Pigeons.jl Documentation](https://julia.pigeons.org/)
- [SplittableRandoms.jl](https://github.com/JuliaRandom/SplittableRandoms.jl)
- [Comrade.jl](https://github.com/ptiede/Comrade.jl)
- Gay.jl: Same SPI pattern for deterministic colors
