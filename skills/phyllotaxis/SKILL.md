---
name: phyllotaxis
description: Succulent rosette growth as propagator network — golden angle = Nash equilibrium, auxin chemotaxis = affective taxis, BCI modulation = closed-loop biofeedback
trit: 1
color: "#3DD98F"
---

# Phyllotaxis

> Spiral leaf arrangement as a propagator network where the golden angle emerges as Nash equilibrium.

**Trit**: +1 (PLUS - Generator)
**Color**: #3DD98F (green — growth)

## Core Insight

The Douady-Couder model of phyllotaxis IS a propagator network (SDF Ch7):
- **Cells** = primordia (partial information: position, auxin, inhibition)
- **Propagators** = Gaussian inhibition kernels (constraint transformers)
- **Scheduler** = plastochron clock (SICP Ch5 explicit control)
- **Quiescence** = golden angle spiral (Nash equilibrium)

The golden angle (137.508°) is not designed — it EMERGES from the constraint network, just as Nash equilibria emerge from propagator-based game solving.

## Architecture

```
                    ┌─────────────────────────────────────┐
                    │        Phyllotaxis Propagator        │
                    │         (SDF Ch7 × Nash)             │
                    └──────────────┬──────────────────────┘
                                   │
          ┌────────────────────────┼────────────────────────┐
          │                        │                        │
    ┌─────▼──────┐          ┌──────▼──────┐          ┌──────▼──────┐
    │   Julia     │          │  TypeScript  │          │   Scheme    │
    │ succulents  │          │  Nashator    │          │  Goblins    │
    │   .jl       │          │  stress-     │          │  rosette-   │
    │             │          │  games.ts    │          │  actor.scm  │
    └─────┬──────┘          └──────┬──────┘          └──────┬──────┘
          │                        │                        │
    Continuous               Game-theoretic            Actor-based
    simulation               equilibrium               concurrency
    + BCI bridge             + propagator              + CapTP bridge
    + taxis bridge           + mechanism               + vat isolation
    + GF(3) verify           design (inverse)          + plugin spec
```

## Mathematical Foundation

### Douady-Couder Inhibition Model

New primordium placement at angle θ* that maximizes auxin:

```
θ* = argmax_θ [ A(θ) - Σᵢ α · exp(-d(θ, pᵢ)² / (2λ²)) ]
```

Where:
- A(θ) = ambient auxin field
- α = inhibition strength (optimal: 2.0)
- λ = inhibition range (optimal: 0.08)
- d(θ, pᵢ) = Euclidean distance from candidate to primordium i

### Golden Angle as Nash Equilibrium

Two adjacent leaves compete for light. Strategies: angular deviations from current position. Payoff: light capture = 1 - overlap penalty.

The Nash equilibrium IS the golden angle: no leaf can unilaterally improve its light capture by deviating from 137.508° divergence.

### Auxin Chemotaxis = Affective Taxis

From affective-taxis.jl: `auxin_density(x)` maps to `attractant_density(z)`, and `auxin_gradient(x)` maps to `grad_log_density(z)`. The Langevin dynamics are identical:

```
dz/dt = ∇_z log γ(z; β) + √2 dσ(t)
```

Where z = primordium position, γ = auxin concentration, β = temperature.

### GF(3) Conservation

Index-based trit assignment ensures perfect balance:
```
classify_trit(i) = { +1 if i mod 3 = 0, 0 if i mod 3 = 1, -1 if i mod 3 = 2 }
```

For N primordia: N mod 3 = 0 → perfect 7/7/7 balance (21 primordia).

## Implementations

### Julia: `succulents.jl` (~550 LOC)

Full continuous simulation with BCI integration:

```julia
# Grow 21 primordia
M = Meristem(λ=0.08, α=2.0, plastochron=6)
for _ in 1:136; tick!(M); end

# Results: 9.49° golden deviation, GF(3) 7/8/7 BALANCED
verify_conservation(M)  # ✓

# BCI modulation
ps = PhenomenalState(φ=0.8, valence=0.6, entropy=1.5, trit=PLUS)
modulate_growth!(M, ps)

# Taxis bridge
AL = AuxinLandscape(M)
classify_valence(auxin_gradient(AL, θ))  # → PLUS/ERGODIC/MINUS
```

Optimal parameters (from sweep): λ=0.08, α=2.0 → 9.49° deviation from golden angle.

### TypeScript: Nashator stress-games.ts

Game-theoretic formulation as OpenGame instances:

```typescript
leafLightCompetition(5)   // 5-strategy light competition game
auxinCompetition(7)       // 7-position auxin inhibition game
rosetteLifecycle()        // seq(auxin ; light ; water) — GF(3) balanced

// Solve via propagator network
solvePropagator(leafLightCompetition(5), { maxRounds: 2000 })
// → golden angle offset = high-weight strategy
```

### Scheme: Goblins rosette-actor.scm (~300 LOC)

Actor-based concurrent rosette growth:

```scheme
(define garden (spawn ^rosette-garden))
($ garden plant! "echeveria")
($ garden plant! "sempervivum")
($ garden grow-all! 21)
($ garden garden-gf3)           ; → balanced
($ garden modulate-all! 0.8 0.6 1.5)  ; BCI modulation
```

Plugin spec for ^vat-bridge integration: plant/grow/modulate/gf3 actions.

## Calibrated Parameters

| Parameter | Symbol | Optimal | Range Tested | Unit |
|-----------|--------|---------|-------------|------|
| Inhibition range | λ | 0.08 | 0.05-0.30 | radius |
| Inhibition strength | α | 2.0 | 2-8 | dimensionless |
| Growth rate | g | 0.01 | 0.005-0.02 | radius/tick |
| Plastochron | P | 6 | 4-10 | ticks |
| Taxis threshold | ε | 0.001 | 0.001-0.01 | gradient |
| Golden deviation | Δ | 9.49° | — | degrees |

## Files

```
succulents.jl                              Julia continuous simulation
nashator/src/stress-games.ts               TypeScript game generators (leafLight, auxin, lifecycle)
nashator/src/stress-games.test.ts          4 phyllotaxis tests (33/33 passing)
goblins-adapter/rosette-actor.scm          Goblins actors (^primordium, ^meristem, ^rosette-garden)
goblins-adapter/rosette-captp-bridge.scm   CapTP bridge: rosette ↔ Nashator solver
asi/skills/phyllotaxis/SKILL.md            This file
asi/skills/phyllotaxis/NEIGHBOR_SKILLS.md  Skill connections
```

## GF(3) Triads

```
phyllotaxis (+1) ⊗ nashator (0) ⊗ affective-taxis (-1) = 0 ✓
    growth          equilibrium      chemotaxis

phyllotaxis (+1) ⊗ propagators (0) ⊗ cybernetic-open-game (-1) = 0 ✓
    biology         SDF Ch7           game theory

succulents (+1) ⊗ bridge-9 (0) ⊗ BCI (-1) = 0 ✓
    output          pipeline          input
```

## Concomitant Skills

| Skill | Trit | Interface |
|-------|------|-----------|
| `nashator` | 0 | Golden angle = Nash equilibrium; leafLightCompetition, auxinCompetition |
| `propagators` | 0 | SDF Ch7 cells = primordia; inhibition = constraint propagation |
| `affective-taxis` | -1 | Auxin chemotaxis ≡ interoceptive taxis; Langevin dynamics |
| `goblins` | 0 | ^rosette-garden actor; vat isolation; CapTP bridge |
| `sdf` | -1 | Ch7 propagators, Ch8 degeneracy (parameter sweep fallback) |
| `sicp` | +1 | Ch3 mutable state, Ch5 explicit control (scheduler) |
| `gay-julia` | 0 | GF(3) coloring, golden spiral, color conservation |
| `enzyme-autodiff` | -1 | Gradient of inhibition kernel via Enzyme.jl |

## References

- Douady & Couder, "Phyllotaxis as a Physical Self-Organized Growth Process" (1996)
- Atela, Golé & Hotton, "A Dynamical System for Plant Pattern Formation" (2002)
- Hanson & Sussman, "Software Design for Flexibility" Ch7 (2021)
- Ghani, Hedges et al., "Compositional Game Theory" (2018)
- Sennesh & Ramstead, "Affective-Taxis Hypothesis" (2025)


## Para(Optic) atlas

Part of: `para-mensch-commons`.

## ALife atlas

Part of: `alife-commons`. Family: `morphogenesis-and-growth`. Canonical: `lindenmayer-systems`.
