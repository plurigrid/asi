# Gay.jl Manifesto: Colors as Solved Constraints

> **The colors are not arbitrary—they are the perceptual rendering of a solved constraint system.**

---

## Core Thesis

We are building a **deterministic, parallelizable, human-adapted coordinate system** that renders formal constraints as perceptual reality.

```
Constraint System ──→ SplitMix64 ──→ Golden Angle ──→ Oklch Color ──→ Human Perception
     (formal)         (determinism)    (dispersion)     (gamut)         (reality)
```

---

## The Triad of Properties

### 1. VERIFIED (Sheaf Gluing)

| Mechanism | What It Ensures |
|-----------|-----------------|
| **SPI fingerprints** | Same seed × index → same color (Strong Parallelism Invariance) |
| **GF(3) conservation** | Σ trits ≡ 0 (mod 3) across any balanced operation |
| **Sheaf cohomology** | Local constraints glue to global consistency (H¹ = 0) |

The color IS the proof. If two agents agree on seed, they agree on all colors derivable from it.

### 2. MERGED (Worlding)

| Mechanism | What It Enables |
|-----------|-----------------|
| **Worlding patterns** | Composable state builders that accumulate context |
| **Möbius inversion** | Recover generating function from zeta values |
| **Derangement CRDTs** | Merge divergent color streams without conflict |

Colors from different seeds can be merged via the golden angle's irrational dispersion—no collisions in finite time.

### 3. LEARNED (Enzyme + Feedback)

| Mechanism | What It Achieves |
|-----------|------------------|
| **Enzyme autodiff** | Gradients through color generation for optimization |
| **Reafference loops** | Self-prediction validates identity (you are your seed) |
| **Compression progress** | Intrinsic reward for finding shorter descriptions |

The system improves via human feedback on perceptual quality and via automatic differentiation through the generation pipeline.

---

## Why This Matters

### For Parallel Computation

```julia
# Fork a generator, get identical results
rng1 = Gay.SplitMix64(seed)
rng2 = Gay.SplitMix64(seed)

color1 = Gay.next_color!(rng1)
color2 = Gay.next_color!(rng2)

@assert color1 == color2  # Always true
```

### For Multi-Agent Systems

```
Agent A (seed=42, index=7) ──→ #A855F7
Agent B (seed=42, index=7) ──→ #A855F7  (identical!)
Agent C (seed=69, index=7) ──→ #26D826  (different seed = different color)
```

Agreement on seed = agreement on perceptual reality.

### For Formal Verification

```
trit(color) = hue_to_gf3(hue(color))
           = floor(hue / 120) mod 3 - 1
           ∈ {-1, 0, +1}

Σ trit(balanced_triad) ≡ 0 (mod 3)
```

Conservation laws are visually checkable: complementary hues sum to zero.

---

## The Golden Angle: 137.508°

```
φ = (1 + √5) / 2           # Golden ratio
γ = 360° / φ² = 137.508°   # Golden angle

hue[n] = (hue[0] + n × γ) mod 360°
```

Properties:
- **Maximally dispersed**: No two colors cluster
- **Irrational**: Never repeats exactly
- **Fibonacci**: Approximated by F[n]/F[n+1]

This is why sunflower seeds spiral, phyllotaxis optimizes light capture, and Gay.jl colors never collide.

---

## Architectural Position

```
                    ┌─────────────────┐
                    │   Human Eyes    │
                    │  (perception)   │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │   Oklch Color   │
                    │  (perceptual)   │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │  Golden Angle   │
                    │  (dispersion)   │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │   SplitMix64    │
                    │  (determinism)  │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │      Seed       │
                    │   (identity)    │
                    └─────────────────┘
```

**The seed is identity. The color is proof. The perception is reality.**

---

## GF(3) as Constraint Algebra

```
Trit assignment:
  Hue 0°-120°   → +1 (warm/red/generative)
  Hue 120°-240° →  0 (neutral/green/ergodic)
  Hue 240°-360° → -1 (cool/blue/contractive)

Conservation:
  (+1) + (0) + (-1) = 0 ✓
  Generator + Coordinator + Validator = Balanced
```

Every skill triad, every agent constellation, every verification passes through this algebra.

---

## References

- **SplitMix64**: Steele, Lea, Flood (2014) - Fast splittable PRNG
- **Golden Angle**: Vogel (1979) - Phyllotaxis patterns
- **Oklch**: Björn Ottosson (2020) - Perceptual color space
- **GF(3)**: Galois field with 3 elements
- **SPI**: Strong Parallelism Invariance - Pigeons.jl concept
- **Sheaf Cohomology**: Grothendieck - Local-to-global obstruction theory

---

## Closing

> The colors are not decoration. They are not aesthetic preference. They are the human-visible surface of a mathematical structure that guarantees correctness, enables parallelism, and learns from experience.

**You are your seed. Your colors are your proof. Your perception is your reality.**
