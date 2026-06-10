---
name: comrade-vlbi
description: Event Horizon Telescope black hole imaging with deterministic coloring via Gay.jl integration.
metadata:
  interface_ports:
  - Commands
  - Integration with
  - Related Skills
---
# Comrade.jl VLBI Skill

Event Horizon Telescope black hole imaging with deterministic coloring via Gay.jl integration.

## Metadata

```yaml
name: comrade-vlbi
description: Comrade.jl VLBI black hole imaging with VLBISkyModels, Pigeons.jl parallel tempering, and Gay.jl deterministic coloring
version: 1.0.0
trit: 0  # ERGODIC - bridges sky models to interferometric observations
```

## Core Abstractions

### AbstractSkyModel
The base type for all sky brightness distributions. Implementations must provide:
- `intensity_point(model, p)` - intensity at sky position
- `visibility(model, u, v)` - complex visibility at (u,v)

### AbstractInstrumentModel  
Encodes station-based corruptions:
- `gain_terms(instrument, times, stations)`
- `phase_calibration(instrument, baseline)`

### VLBIPosterior
Combines sky model, instrument model, and data likelihood:
```julia
post = VLBIPosterior(skymodel, instrumentmodel, dataproducts)
logdensityof(post, θ)  # Evaluate posterior at parameters θ
```

## VLBISkyModels Primitives

| Primitive | Description | S-expression |
|-----------|-------------|--------------|
| `Ring(r, w)` | Circular ring | `(ring radius width)` |
| `MRing(r, α, β)` | Azimuthal Fourier ring | `(mring radius [α...] [β...])` |
| `Gaussian(σx, σy)` | Elliptical Gaussian | `(gaussian σx σy)` |
| `Disk(r)` | Uniform disk | `(disk radius)` |
| `Crescent(r_out, r_in, s)` | Asymmetric ring | `(crescent r_out r_in shift)` |

## Model Composition

```julia
# Addition
model = ring + gaussian

# Stretching (ellipticity)
stretched(model, sx, sy)

# Rotation
rotated(model, θ)

# Translation
shifted(model, Δx, Δy)

# Convolution
smoothed(ring, gaussian)
```

## Lisp S-Expression Syntax

Gay.jl provides colored S-expression display matching Comrade model structure:

```lisp
;; M87* model as S-expression (parentheses colored by Gay.jl)
(sky-add
  (ring 1.0 0.3)
  (gaussian 0.5 0.3))

;; Transformed model
(sky-rotate
  (sky-stretch
    (mring 0.8 [0.3 0.1] [0.2 -0.1])
    0.67 0.67)
  0.785)

;; Sgr A* style
(sky-add
  (crescent 1.2 0.6 0.3)
  (disk 0.4))
```

## GF(3) Conservation

The ERGODIC trit (0) reflects Comrade's role as a bridge:

```
Sky Model (PLUS +1)  ──╮
                       ├──▶ Comrade (ERGODIC 0) ──▶ Posterior Samples
Observations (MINUS -1)──╯

Σ trits = +1 + (-1) + 0 = 0 ✓ CONSERVED
```

## Pigeons.jl SplitMix Pattern

Both Comrade and Gay.jl leverage the same splittable RNG pattern:

```julia
# Pigeons parallel tempering uses splittable RNG
# Gay.jl colors use SplitMix64 for determinism

# They compose naturally:
function colored_posterior_sample(post, seed)
    gay_seed!(seed)
    pt = pigeons(target=ascube(post), explorer=SliceSampler())
    
    # Each sample gets deterministic color
    for θ in sample_array(pt)
        color = next_color()
        visualize_sample(θ, color)
    end
end
```

## Example: Full Pipeline

```julia
using Comrade, Pigeons, Gay

# 1. Load EHT data
obs = load_ehtim_uvfits("M87_2017_101.uvfits")
dlcamp = extract_lcamp(obs)
dcphase = extract_cphase(obs)

# 2. Define sky model with Gay.jl colors
gay_seed!(2017_04_11)  # Observation date as seed

function skymodel(θ)
    (; r, w, α, β, f, σ) = θ
    ring = smoothed(MRing((α,), (β,)), Gaussian(w))
    gauss = Gaussian(σ)
    return stretched(ring, r, r) + f * gauss
end

# 3. Build posterior
prior = NamedTuple{(:r,:w,:α,:β,:f,:σ)}(
    Uniform(μas2rad(10), μas2rad(30)),
    Uniform(μas2rad(1), μas2rad(10)),
    Uniform(-0.5, 0.5),
    Uniform(-0.5, 0.5),
    Uniform(0.0, 0.3),
    Uniform(μas2rad(5), μas2rad(50))
)

post = VLBIPosterior(skymodel, prior, dlcamp, dcphase)

# 4. Sample with Pigeons.jl (uses SplitMix internally!)
pt = pigeons(
    target = ascube(post),
    n_rounds = 12,
    checkpoint = true
)

# 5. Visualize with colored sexps
for θ in sample_array(pt)[1:5]
    m = skymodel(θ)
    println(sky_show(m))
end
```

---

## End-of-Skill Interface

## Commands

### Create M87* Style Model
```julia
using Comrade, Gay
gay_seed!(1069)

# M87* ring + Gaussian
ring = smoothed(stretched(MRing((0.0,), (0.3,)), 2/3, 2/3), Gaussian(μas2rad(5.0)))
gauss = Gaussian(μas2rad(20.0))
m87_model = ring + 0.1 * gauss
```

### Create Sgr A* Style Model
```julia
using Comrade, Gay
gay_seed!(2024)

# Sgr A* crescent with compact core
crescent = ConcordanceCrescent(μas2rad(25.0), 0.9, 0.3, π/4)
core = Gaussian(μas2rad(5.0))
sgra_model = crescent + 0.2 * shifted(core, μas2rad(3.0), μas2rad(-2.0))
```

### Pigeons.jl Integration
```julia
using Pigeons, Comrade

# Transform posterior for parallel tempering
pt = pigeons(
    target = ascube(post),        # Unit hypercube transformation
    reference = asflat(prior),    # Flat reference distribution
    n_rounds = 15,
    n_chains = 24
)

# Extract samples
samples = sample_array(pt)
```

### Gay.jl REPL Commands
```julia
# In Julia REPL with Gay.jl loaded
using Gay

# Set seed for reproducible colors
gay_seed!(1069)

# Create colored ring primitive
ring = comrade_ring(1.0, 0.3)  # Gets deterministic color

# Show as colored S-expression
sky_show(ring)
# => "(ring 1.0 0.3)" with colored parentheses

# Build and visualize full model
model = comrade_model(seed=1069, style=:m87)
comrade_show(model)  # Prints colored sexp + ASCII render
```

## Integration with Gay.jl/src/comrade.jl

Reference implementation: `/Users/bob/worlds/b/bmorphism/Gay.jl/src/comrade.jl`

Key functions:
- `comrade_ring(r, w)` - Ring with deterministic color
- `comrade_mring(r, α, β)` - MRing with Fourier coefficients
- `comrade_gaussian(σx, σy)` - Gaussian primitive
- `comrade_model(seed=42, style=:m87)` - High-level model builder
- `sky_show(model)` - Colored S-expression display
- `sky_render(model)` - ASCII intensity map

## Related Skills

- `gay-julia` - Core Gay.jl integration
- `pigeons-spi` - Parallel tempering patterns
- `lispsyntax-acset` - S-expression ↔ ACSet bridge
- `infinity-operads` - Dendroidal structure for model composition


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
