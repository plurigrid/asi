# Plurigrid ASI - gay branch

**SplitMixTernary**: GF(3)-balanced splittable random streams extending SplittableRandoms.jl.

## Purpose

This branch focuses on **ternary extensions** to splittable random number generation:

1. **SplitMixTernary algorithm** - Three parallel streams with GF(3) conservation
2. **Extension proposal for SplittableRandoms.jl** - `split3()` API
3. **Verified properties** - Dafny + Narya proofs

## Core Algorithm

```julia
# Three streams from one seed
const STREAM_MINUS   = 0x243f6a8885a308d3  # π
const STREAM_ERGODIC = 0xb7e151628aed2a6a  # e  
const STREAM_PLUS    = 0x452821e638d01377  # √2

function split3(seed::UInt64)
    base = splitmix64(seed)
    (
        splitmix64(base ⊻ STREAM_MINUS),   # -1 stream
        splitmix64(base ⊻ STREAM_ERGODIC), #  0 stream
        splitmix64(base ⊻ STREAM_PLUS)     # +1 stream
    )
end
```

## Skill Triads

### SplitMixTernary Triad

| Skill | Trit | Description |
|-------|------|-------------|
| `splitmix-ternary` | 0 | Core ternary RNG algorithm |
| `spi-parallel-verify` | -1 | Verification tooling |
| `triad-interleave` | +1 | Stream interleaving |

**Sum: 0** ✓ GF(3) conserved

### BB(6) Oracle Triad

| Skill | Trit | Description |
|-------|------|-------------|
| `busy-beaver-oracle` | +1 | Generate BB(n) lower bound proofs |
| `levin-levity` | 0 | Nash equilibrium + WEV |
| `prediction-market-oracle` | -1 | Market-making |

**Sum: 0** ✓ GF(3) conserved

## Skills

| Skill | Origin | Description |
|-------|--------|-------------|
| `splitmix-ternary` | new | SplittableRandoms.jl extension |
| `unison-acset` | PR #36 | ACSet-structured docs, seed 1069 |
| `markov-game-acset` | PR #34 | Markov games with derangement |
| `rama-gay-zig` | PR #37 | Gay.jl + Rama + Zig triad |
| `levin-levity` | original | Levin search + WEV extraction |
| `autopoiesis` | original | Self-modifying config |
| `open-games` | original | Compositional game theory |
| `bisimulation-game` | original | Skill dispersal |
| `world-hopping` | original | Possible world navigation |

## SplitMix64 Constants

```
GOLDEN = 0x9e3779b97f4a7c15
MIX1   = 0xbf58476d1ce4e5b9
MIX2   = 0x94d049bb133111eb
SEED   = 0x42D (1069)
```

## Verified Properties

| Property | Dafny | Narya |
|----------|-------|-------|
| Determinism | ✅ `SplitMixTernary.dfy` | ✅ `spi_conservation.ny` |
| Path invariance | ✅ | — |
| GF(3) conservation | ✅ | ✅ `gf3.ny` |
| Reafference closure | ✅ `GayMcpCriticalProofs.dfy` | ✅ |

## SplittableRandoms.jl Extension Proposal

```julia
# Proposed additions to SplittableRandoms.jl

struct SplittableRandom3
    minus::SplittableRandom
    ergodic::SplittableRandom
    plus::SplittableRandom
end

split3(rng::SplittableRandom)::SplittableRandom3
trit(sr3::SplittableRandom3)::Int  # -1, 0, or +1
rand_trit(sr3::SplittableRandom3)::Symbol
```

## Installation

```bash
git clone https://github.com/plurigrid/asi -b gay
cd asi
amp skill splitmix-ternary
```

## Related

- [Gay.jl](https://github.com/bmorphism/Gay.jl) - Reference implementation
- [SplittableRandoms.jl](https://github.com/JuliaMath/SplittableRandoms.jl) - Base library
- [Pigeons.jl](https://pigeons.run) - SPI inspiration

## License

Apache-2.0

---

*"In the ternary splitting, the colors find their balance."*
