# Phyllotaxis — Neighbor Skills

## Direct Neighbors (shared code/data)

| Skill | Trit | Shared Interface | Files |
|-------|------|-----------------|-------|
| nashator | 0 | `leafLightCompetition()`, `auxinCompetition()`, `rosetteLifecycle()` | `stress-games.ts` |
| propagators | 0 | Cell/Propagator/Scheduler pattern, bidirectional constraint flow | `propagator.ts`, `propagator-nash.scm` |
| goblins | 0 | `^primordium`, `^meristem`, `^rosette-garden`, plugin spec | `rosette-actor.scm` |
| affective-taxis | -1 | `AuxinLandscape` ≡ `TaxisLandscape`, gradient = valence | `succulents.jl`, `affective-taxis.jl` |

## Conceptual Neighbors (shared math)

| Skill | Trit | Connection |
|-------|------|------------|
| sdf | -1 | Ch7 propagator formalism is the implementation foundation |
| sicp | +1 | Ch3 state (mutable primordia), Ch5 explicit control (scheduler) |
| open-games | +1 | Hedges-Ghani compositional games: `seq(auxin; light; water)` |
| gay-julia | 0 | Golden spiral coloring, GF(3) conservation, SplitMix64 |
| enzyme-autodiff | -1 | Gradient of Gaussian inhibition kernel for optimal placement |
| langevin-dynamics | -1 | Auxin transport = Langevin diffusion on concentration landscape |
| bridge-9 | 0 | BCI phenomenal state → growth modulation → color feedback |
| captp | 0 | CapTP session bridge: rosette actors ↔ remote Nashator solver |

## Balanced Triads

```
phyllotaxis (+1) + nashator (0) + affective-taxis (-1) = 0
phyllotaxis (+1) + propagators (0) + sdf (-1) = 0
phyllotaxis (+1) + goblins (0) + langevin-dynamics (-1) = 0
phyllotaxis (+1) + bridge-9 (0) + enzyme-autodiff (-1) = 0
phyllotaxis (+1) + gay-julia (0) + open-games... wait, open-games is +1
```

Corrected triads (sum = 0 mod 3):
```
phyllotaxis (+1) + nashator (0) + affective-taxis (-1) = 0   ✓
phyllotaxis (+1) + propagators (0) + sdf (-1) = 0             ✓
phyllotaxis (+1) + goblins (0) + langevin-dynamics (-1) = 0   ✓
phyllotaxis (+1) + bridge-9 (0) + enzyme-autodiff (-1) = 0    ✓
phyllotaxis (+1) + captp (0) + cybernetic-open-game (0) = 1   ✗ — needs -1 balancer
```

## Data Flow

```
BCI (EEG)
  ↓ Fisher-Rao
PhenomenalState(φ, valence, entropy)
  ↓ bridge-9
modulate_growth!(Meristem, ps)     ← succulents.jl
  ↓ tick loop
Primordium positions {θ, r, trit}
  ↓ auxin landscape
AuxinLandscape → classify_valence  ← affective-taxis bridge
  ↓ game extraction
leafLightCompetition(N)            ← nashator stress-games.ts
  ↓ propagator solve
Nash equilibrium σ*                ← propagator.ts
  ↓ CapTP bridge
^rosette-garden modulate!          ← rosette-actor.scm
  ↓ GF(3) check
garden-gf3 → balanced?            ← conservation verification
  ↓ color
trit-color → NATS → Emacs         ← color pipeline
```
