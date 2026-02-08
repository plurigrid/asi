# splitmix-ternary

SplitMixTernary: Extension of SplittableRandoms.jl for GF(3) balanced streams.

## Overview

Extends [SplittableRandoms.jl](https://github.com/JuliaMath/SplittableRandoms.jl) with a ternary stream mode that generates **three parallel, independent streams** with GF(3) conservation guarantees.

## The Gap

SplittableRandoms.jl provides:
- Binary splitting: `split(rng) → (rng1, rng2)`
- Strong Parallelism Invariance (SPI)
- Deterministic parallel execution

**Missing**: Ternary splitting with GF(3) balance for triadic systems.

## Proposed Extension

```julia
# Current binary split
rng1, rng2 = split(rng)

# Proposed ternary split (this skill)
minus, ergodic, plus = split3(rng)  # GF(3) balanced

# Each stream tagged with trit
trit(minus) == -1
trit(ergodic) == 0
trit(plus) == +1
```

## SplitMixTernary Algorithm

```julia
const STREAM_MINUS   = 0x243f6a8885a308d3  # π fractional bits
const STREAM_ERGODIC = 0xb7e151628aed2a6a  # e fractional bits  
const STREAM_PLUS    = 0x452821e638d01377  # √2 fractional bits

function split3(seed::UInt64)
    base = splitmix64(seed)
    (
        splitmix64(base ⊻ STREAM_MINUS),
        splitmix64(base ⊻ STREAM_ERGODIC),
        splitmix64(base ⊻ STREAM_PLUS)
    )
end
```

## Majority Vote Trit Generation

```julia
function next_trit(minus::UInt64, ergodic::UInt64, plus::UInt64)
    v_m = (splitmix64(minus) >> 63) & 1
    v_e = (splitmix64(ergodic) >> 63) & 1
    v_p = (splitmix64(plus) >> 63) & 1
    
    votes = Int(v_p) - Int(v_m)
    if votes > 0
        :plus
    elseif votes < 0
        :minus
    elseif v_e == 1
        :ergodic
    elseif v_p == 1
        :plus
    else
        :minus
    end
end
```

## GF(3) Conservation Guarantee

For any sequence of N trits generated:
```
Σᵢ trit_value(tᵢ) ≡ 0 (mod 3)  as N → ∞
```

Statistical property, not per-step guarantee.

## API Proposal for SplittableRandoms.jl

```julia
# New types
struct SplittableRandom3
    minus::SplittableRandom
    ergodic::SplittableRandom
    plus::SplittableRandom
end

# New functions
split3(rng::SplittableRandom)::SplittableRandom3
trit(sr3::SplittableRandom3)::Int  # Returns -1, 0, or +1
rand_trit(sr3::SplittableRandom3)::Symbol  # :minus, :ergodic, :plus

# Interop with existing API
Base.rand(sr3::SplittableRandom3) = rand(sr3.ergodic)
split(sr3::SplittableRandom3) = split3(sr3.ergodic)
```

## Verified Properties (Dafny)

From `verification/dafny/SplitMixTernary.dfy`:

| Property | Lemma | Status |
|----------|-------|--------|
| Determinism | `Determinism(seed, n)` | ✅ |
| Path invariance | `PathInvariance(state, m, n)` | ✅ |
| GF(3) conservation | `GF3AlwaysConserved(trit)` | ✅ |
| Bounded output | `BoundedOutput(trit, limit)` | ✅ |

## Use Cases

### Triadic Agent Systems
```julia
seeds = split3(master_seed)
validator = Agent(seeds[1], :minus)    # -1
coordinator = Agent(seeds[2], :ergodic) # 0
generator = Agent(seeds[3], :plus)      # +1
# Sum: 0 ✓
```

### Monte Carlo with GF(3) Balance
```julia
for sweep in 1:n_sweeps
    trit = next_trit(state...)
    if trit == :plus
        propose_addition!()
    elseif trit == :minus
        propose_deletion!()
    else
        propose_exchange!()
    end
end
```

### Checkerboard Decomposition
```julia
lattice = gay_checkerboard_2d(interleaver, Lx, Ly)
# Sites colored by (i+j) mod 3 using ternary streams
```

## Implementation Status

| Component | Location | Status |
|-----------|----------|--------|
| Core algorithm | `Gay.jl/src/splittable.jl` | ✅ |
| Dafny proofs | `Gay.jl/verification/dafny/SplitMixTernary.dfy` | ✅ |
| Narya proofs | `Gay.jl/verification/narya/spi_conservation.ny` | ✅ |
| SplittableRandoms.jl PR | — | 📋 Planned |

## GF(3) Trit

| Role | Trit | Description |
|------|------|-------------|
| Algorithm | -1 | SplitMix64 core |
| Coordination | 0 | Stream balancing (ergodic) |
| Generation | +1 | Color/trit output |

## References

- [SplittableRandoms.jl](https://github.com/JuliaMath/SplittableRandoms.jl)
- [Pigeons.jl SPI](https://pigeons.run/dev/parallel/#Strong-parallelism-invariant)
- [Gay.jl verification/dafny/SplitMixTernary.dfy](https://github.com/bmorphism/Gay.jl)
- Steele et al. (2014) "Fast Splittable Pseudorandom Number Generators"

## Related Skills

- `gay-julia` - Wide-gamut color with SPI
- `spi-parallel-verify` - Verification tooling
- `gf3-pr-verify` - PR conservation checking
- `triad-interleave` - Stream interleaving
