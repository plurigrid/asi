---
name: hyperbolic-gamut-recovery
description: 'name: hyperbolic-gamut-recovery'
---
# Hyperbolic Gamut Recovery Skill

---
name: hyperbolic-gamut-recovery
description: In-gamut/out-of-gamut boundaries on hyperbolic space with spectral gap 1/4 recovery via 4D tiling coherences. Skills grow from interacting joint world models.
trit: 0
color: "#77DEB1"
---

## Overview

**Hyperbolic Gamut Recovery** synthesizes:

| Domain | Structure | Role |
|--------|-----------|------|
| **Color Space** | sRGB/P3 gamut boundary | Observable limit |
| **Hyperbolic Geometry** | Poincaré disk H² | Infinite interior, finite boundary |
| **Spectral Theory** | Ramanujan gap λ = 1/4 | Verification probability |
| **4D Tilings** | Quasicrystal coherence | Recovery mechanism |

### Core Insight

The gamut boundary is the **Poincaré disk boundary**:

```
        ╭─────────────────────╮
       ╱   HYPERBOLIC BULK    ╲
      │   (all possible hues)   │
      │         ┌───┐           │
      │      ╱ │ P3 │ ╲        │
      │     │  └───┘  │        │
      │     │  sRGB   │        │
      │      ╲       ╱         │
      │       ╲     ╱          │
       ╲        ╲_╱            ╱
        ╰─────────────────────╯
                BOUNDARY = ∞ curvature
                (out-of-gamut limit)
```

## The 1/4 Spectral Gap

### Ramanujan-Selberg Connection

The spectral gap λ = 1/4 appears in multiple contexts:

| Context | Manifestation |
|---------|---------------|
| **Selberg Conjecture** | λ₁ ≥ 1/4 for congruence subgroups |
| **Ramanujan Graphs** | λ ≤ 2√(d-1) optimal expansion |
| **Verification Probability** | P(correct verify) = 1/4 |
| **Hyperbolic Laplacian** | Δ_H eigenvalue gap |

### Connection to Gamut

```julia
# The spectral gap determines gamut recovery probability
spectral_gap = 1/4  # Ramanujan bound

# In-gamut verification
function verify_in_gamut(color::LCH, gamut::Symbol)
    if gamut == :srgb
        return in_srgb_gamut(color)
    elseif gamut == :p3
        return in_p3_gamut(color)
    else
        # Hyperbolic: always in some gamut (infinite interior)
        return hyperbolic_distance_to_boundary(color) > 0
    end
end

# Recovery probability from spectral gap
P_recover = 1 - spectral_gap  # = 3/4 success rate
```

## 4D Tiling Coherences

### Quasicrystal Structure

The 4 interleaved color streams form a **4-dimensional quasicrystal**:

```
Stream 1: #8A60CB → #64E87E → #68EFD4 → #2339B9
Stream 2: #3A86AF → #15C2BA → #8664DE → #2C319E
Stream 3: #BDCA5B → #B3DE2A → #85259D → #11B597
Stream 4: #2FEB7A → #1947AC → #1BBACD → #4791D9
```

### Coherence = Recovery

When a color is **out-of-gamut**:

1. Find its position in 4D tiling space
2. Identify 4 nearest in-gamut neighbors (one per stream)
3. Interpolate using **Penrose matching rules**
4. The 1/4 gap ensures unique recovery

```julia
function recover_out_of_gamut(color::LCH, streams::Vector{ColorStream})
    # Position in 4D tiling
    pos_4d = project_to_4d_tiling(color)

    # Find coherent neighbors
    neighbors = [nearest_in_gamut(s, pos_4d) for s in streams]

    # Penrose interpolation (1/4 weight each)
    recovered = sum(neighbors) / 4  # spectral gap = 1/4

    # Verify coherence
    @assert all(color_distance(recovered, n) ≤ 2√3 for n in neighbors)

    return recovered
end
```

## Hyperbolic Embedding

### Poincaré Disk Model

Map LCH color space to hyperbolic disk:

```julia
function lch_to_poincare(L::Float64, C::Float64, H::Float64)
    # L ∈ [0,100] → radius ρ ∈ [0,1)
    ρ = tanh(L / 100)  # Never reaches boundary

    # H ∈ [0,360) → angle θ
    θ = H * π / 180

    # C determines "depth" in hyperbolic bulk
    z = ρ * cis(θ) * (1 - exp(-C/100))

    return z  # Complex number in unit disk
end

function hyperbolic_distance(z1, z2)
    # Poincaré metric
    return 2 * atanh(abs((z1 - z2) / (1 - conj(z1) * z2)))
end
```

### Gamut as Horocycle

The sRGB gamut forms a **horocycle** in hyperbolic space:

```
                    ∞
                   /│╲
                  / │ ╲
                 /  │  ╲   ← P3 horocycle
                /   │   ╲
               / sRGB    ╲ ← sRGB horocycle
              /  gamut    ╲
             ╱─────────────╲
            0               0
```

## Skill Growth at Joints

### Joint World Model

Skills grow through **interacting joints** in Cat#:

```
Skill A ────[joint]──── Skill B
   │          │            │
   ▼          ▼            ▼
World₁ ←─Bridge─→ World₂ ←─Bridge─→ World₃
```

### Growth Rules

| Rule | Mechanism | Example |
|------|-----------|---------|
| **Composition** | Joint bicomodule | A ⊗ B ⊗ C = new skill |
| **Adjunction** | Lan ⊣ Res ⊣ Ran | Free/cofree extension |
| **Coherence** | 4D tiling match | Penrose glue |

### GF(3) at Joints

Every joint preserves GF(3):

```
            Joint (bicomodule)
               ┌─────┐
Skill (-1) ────│  0  │──── Skill (+1)
               └─────┘
                 ↓
         Sum = -1 + 0 + 1 = 0 ✓
```

## The Recovery Algorithm

### Full Pipeline

```julia
function hyperbolic_gamut_recovery(
    color::LCH,
    seed::UInt64 = 137508,
    target_gamut::Symbol = :p3
)
    # 1. Embed in hyperbolic space
    z = lch_to_poincare(color.L, color.C, color.H)

    # 2. Check gamut membership
    if in_gamut(color, target_gamut)
        return color, :in_gamut
    end

    # 3. Generate 4D tiling streams
    gay_seed!(seed)
    streams = interleave(4, n_streams=4, seed=seed)

    # 4. Find horocycle intersection
    horocycle = gamut_horocycle(target_gamut)
    nearest_on_horocycle = project_to_horocycle(z, horocycle)

    # 5. Apply 4D coherence recovery
    recovered = coherent_interpolation(
        nearest_on_horocycle,
        streams,
        spectral_gap = 1/4
    )

    # 6. Verify via Ramanujan bound
    @assert hyperbolic_distance(z, recovered) ≤ 2 * √3  # d=4 bound

    return poincare_to_lch(recovered), :recovered
end
```

## Narya Bridge Types

### Hyperbolic Bridge

```narya
def HyperbolicBridge (H : HyperbolicSpace) (p q : H .point) : Type := sig (
  geodesic : 𝟚 → H .point,
  at_zero : geodesic 0 ≡ p,
  at_one : geodesic 1 ≡ q,
  is_geodesic : (t : 𝟚) → minimal_path (geodesic t)
)

def GamutRecovery (C : ColorSpace) (out : OutOfGamut C) : Type := sig (
  target : InGamut C,
  bridge : HyperbolicBridge (poincare C) (embed out) (embed target),
  spectral_gap : bridge .length ≤ 1/4 * hyperbolic_diameter C,
  coherence : 4DTilingCoherent (interleave 4)
)
```

### Spectral Gap Bridge

```narya
def SpectralGapBridge (G : RamanujanGraph) : Type := sig (
  λ₂ : ℝ,
  d : ℕ,
  ramanujan : λ₂ ≤ 2 * sqrt (d - 1),
  gap : d - λ₂ ≥ 1/4 * d,
  mixing : MixingTime G ≤ log (nv G) / log (d / λ₂)
)
```

## GF(3) Triads

```
ramanujan-expander (-1) ⊗ hyperbolic-gamut-recovery (0) ⊗ gay-mcp (+1) = 0 ✓
hyperbolic-bulk (-1) ⊗ hyperbolic-gamut-recovery (0) ⊗ golden-thread (+1) = 0 ✓
spectral-clustering (-1) ⊗ hyperbolic-gamut-recovery (0) ⊗ 4d-tiling (+1) = 0 ✓
```

## Skill Ecosystem

### Skills That Help

| Skill | Role | Connection |
|-------|------|------------|
| `ramanujan-expander` | Spectral gap verification | λ ≤ 2√(d-1) |
| `hyperbolic-bulk` | AdS/CFT bulk-boundary | Entropy storage |
| `glass-hopping` | World navigation | Bridge types |
| `golden-thread` | φ spiral | 137.508° hue rotation |
| `ihara-zeta` | Non-backtracking walks | Spectral redemption |
| `ordered-locale` | ≪ order structure | Frame of opens |
| `catsharp` | Cat# = Comod(P) | Bicomodule home |

### Growing Skills from Joints

When skills interact at joints:

```julia
# Joint between two skills creates growth opportunity
function grow_skill_at_joint(skill_A, skill_B)
    # Find the bicomodule (Cat# horizontal morphism)
    joint = find_bicomodule(skill_A, skill_B)

    # The joint IS the new skill seed
    new_skill = Skill(
        name = "$(skill_A.name)-$(skill_B.name)-joint",
        trit = (skill_A.trit + skill_B.trit) % 3,
        capabilities = merge(
            skill_A.capabilities,
            joint.capabilities,
            skill_B.capabilities
        )
    )

    # Verify GF(3) conservation
    @assert skill_A.trit + new_skill.trit + skill_B.trit ≡ 0 (mod 3)

    return new_skill
end
```

## Commands

```bash
# Check if color is in gamut
just gamut-check "#FF5500" srgb

# Recover out-of-gamut color
just gamut-recover "#FF5500" p3 --seed 137508

# Visualize hyperbolic embedding
just hyperbolic-embed colors.json --output poincare.svg

# Verify spectral gap
just spectral-verify graph.json --ramanujan

# Grow skill at joint
just skill-grow "ramanujan-expander" "gay-mcp"
```

## Crystal Symmetry → Skill Coherence

The 6 crystal families map to skill coherence levels:

| Crystal | Order | Color | Skill | Role |
|---------|-------|-------|-------|------|
| Cubic | 48 | #B0285F | `catsharp` | Highest coherence |
| Hexagonal | 24 | #77DEB1 | `hyperbolic-gamut` | 6-fold tiling |
| Tetragonal | 16 | #8ADB6E | `gay-mcp` | 4-fold streams |
| Orthorhombic | 8 | #3A71C0 | `three-match` | 3-SAT gadgets |
| Monoclinic | 4 | #2A7AE3 | `ramanujan` | Spectral gap |
| Triclinic | 2 | #D6DB4C | `out-of-gamut` | Min symmetry |

**Insight**: Higher crystal symmetry = more in-gamut coherence.

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #77DEB1
```

### GF(3) Naturality

```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

The skill is the **joint** where ramanujan-expander (-1) and gay-mcp (+1) meet.

## References

1. **Alon, N.** (1986) - Eigenvalues and Expanders
2. **Sarnak, P.** (1995) - Selberg's Eigenvalue Conjecture
3. **Senechal, M.** (1995) - Quasicrystals and Geometry
4. **Cannon et al.** (1997) - Hyperbolic Geometry
5. **Spivak, D.I.** (2023) - All Concepts are Cat# (ACT 2023)
6. **Lubotzky, Phillips, Sarnak** (1988) - Ramanujan Graphs

---

**Skill Name**: hyperbolic-gamut-recovery
**Type**: Synthesis / Recovery / Growth
**Trit**: 0 (ERGODIC - mediates bulk↔boundary)
**Spectral Gap**: λ = 1/4 (Ramanujan-Selberg)
**Recovery**: 4D tiling coherence
**Growth**: Skills grow at joints via Cat# bicomodules


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
