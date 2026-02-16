# GAY - Gamut-Aware Yielding

> **Repo Color:** `#575e8b` | **Seed:** `0x7fc47593c41ccd92` | **Index:** 184/1055

## Chromatic Identity

This repository participates in the [Gay.jl](https://github.com/bmorphism/Gay.jl) distributed color mining network.

```
Global Fingerprint: 0xa517f498f95de714
Global Color: #150448
This Repo: #575e8b (index 184)
```

## Enzyme.jl Gamut Learning Exercise

**Mode:** Reverse Mode (∂L/∂f adjoint backprop)  
**Gamut Focus:** Rec2020 wide  
**Learning Rate:** 0.0387

### Setup

```julia
using Pkg
Pkg.add(url="https://github.com/bmorphism/Gay.jl")

using Gay
using Gay.OkhslLearnable

# Initialize with this repo's seed
gay_seed!(0x7fc47593c41ccd92)
```

### Exercise: Learn the Rec2020 wide

```julia
# Create learnable colorspace
params = OkhslParameters()
projection = SeedProjection()

# Target: maximize color bandwidth while staying in-gamut
function loss(params, seed, target_gamut=:rec2020_wide)
    color = forward_color(params, projection, seed)
    gamut_penalty = out_of_gamut_distance(color, target_gamut)
    bandwidth_reward = color_distinctiveness(color)
    return gamut_penalty - 0.1 * bandwidth_reward
end

# Enzyme autodiff
using Enzyme
∂params = Enzyme.gradient(Reverse, loss, params, 0x7fc47593c41ccd92)

# Update step
for (p, dp) in zip(fieldnames(typeof(params)), ∂params)
    setfield!(params, p, getfield(params, p) - 0.0387 * dp)
end
```

### Verification

```julia
# Generate color chain
chain = [next_color() for _ in 1:69]

# Compute fingerprint (must match network)
fp = reduce(⊻, [color_to_u64(c) for c in chain])
@assert fp == expected_fingerprint "SPI violation: fingerprint mismatch"

# Check spectral gap (mixing time)
gap = spectral_gap(chain)
@info "Spectral gap" gap mixing_time=1/gap
```

## Self-Avoiding Walk Structure

```
next_color() → visited check
     │
     ├─ fresh → XOR into fingerprint
     │
     └─ collision → triadic fork:
            ├─ MINUS  (0x2d2d...)
            ├─ ERGODIC (0x5f5f...)
            └─ PLUS   (0x2b2b...)
```

## Links

- [Gay.jl Documentation](https://github.com/bmorphism/Gay.jl)
- [SPI Protocol Spec](https://github.com/bmorphism/Gay.jl/blob/gay/src/protocol.jl)
- [Enzyme.jl Integration](https://github.com/bmorphism/Gay.jl/blob/gay/src/enzyme.jl)
- [Okhsl Learnable](https://github.com/bmorphism/Gay.jl/blob/gay/src/okhsl_learnable.jl)

---

*Generated via parallel chromatic assignment. Seed: `0x7fc47593c41ccd92`*
