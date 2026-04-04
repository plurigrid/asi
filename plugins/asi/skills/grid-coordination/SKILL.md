# grid-coordination

Microgrid-inspired coordination framework: Grid-Forming (GFM) vs Grid-Following (GFL) agents with spectral gap 1/4 benchmark for direction entropy justifiability.

## Core Concept

In microgrids:
- **Grid-Forming (GFM)** inverters: Set voltage/frequency reference (leader)
- **Grid-Following (GFL)** inverters: Synchronize to existing reference (follower)

In coordination:
- **GFM agents**: Set specification rate (drift component, deterministic)
- **GFL agents**: Track direction entropy (diffusion component, stochastic)
- **Spectral gap 1/4**: The Ramanujan benchmark for optimal mixing

## Key Formula: Justifiability

```
Direction entropy is JUSTIFIED when:
    H(direction) ≈ specification_rate / gap_benchmark

At gap = 0.25 (Ramanujan optimal):
    H_justified = S / 0.25 = 4 × S

Justifiability Score:
    J = 1 - |H - H_justified| / max(H, H_justified)
```

## Usage

```bash
# Run the demo
cd ~/Gay.jl && julia examples/grid_coordination_demo.jl

# In Julia REPL
include("src/grid_coordination.jl")
states = simulate_coordination(
    potential = x -> 0.5 * sum(x.^2),  # Single well
    gfm_initial = [2.0, 1.0],
    gfl_initial = [-1.0, -0.5],
    diffusion_strength = 0.4,
    gap = 0.25,  # Ramanujan benchmark
    dt = 0.01,
    T = 5.0
)
println(coordination_report(states))
```

## Agent Types

### GridFormingAgent (GFM)
```julia
mutable struct GridFormingAgent <: CoordinationAgent
    specification_rate::Float64    # Constraint generation (bits/τ)
    potential::Function            # V(x): energy landscape
    state::Vector{Float64}         # Current position
end
```
- **Role**: Creates the reference frame (like GFM inverter sets voltage)
- **Dynamics**: Pure drift `dx = -∇V dt`
- **Metric**: Specification rate S = |∇²V| / log(2)

### GridFollowingAgent (GFL)
```julia
mutable struct GridFollowingAgent <: CoordinationAgent
    direction_entropy::Float64     # H(direction) in bits
    diffusion_strength::Float64    # σ² noise intensity
    state::Vector{Float64}
    reference_agent::GridFormingAgent
end
```
- **Role**: Synchronizes to reference (like GFL inverter locks to grid)
- **Dynamics**: Drift + diffusion `dx = -∇V dt + σ√(gap) dW`
- **Metric**: Direction entropy H = -Σ pᵢ log₂(pᵢ)

## Spectral Gap Benchmark

| Gap | Interpretation | Mixing Time | Justifiability |
|-----|----------------|-------------|----------------|
| < 0.1 | Tangled, slow mixing | > 10τ | Over-exploring |
| **0.25** | **Ramanujan optimal** | **4τ** | **Aligned** |
| > 0.5 | Over-connected | < 2τ | Under-exploring |

## GF(3) Integration

Justifiability maps to triadic coloring:

```julia
function gf3_trit(J::Float64)
    J >= 0.67 → :PLUS     # GFM dominant (warm, 330°)
    J >= 0.33 → :ERGODIC  # Balanced (neutral, 120°)
    J <  0.33 → :MINUS    # GFL dominant (cold, 240°)
end
```

Conservation: Across parallel coordination streams, Σ trits ≡ 0 (mod 3)

## Fokker-Planck Connection

The GFM-GFL dynamics are the agent-level realization of Fokker-Planck:

```
∂ρ/∂t = -∇·(μρ) + ∇·(D∇ρ)
         ↑ GFM      ↑ GFL
        drift    diffusion
```

- **Drift μ = -∇V**: GFM sets the deterministic flow
- **Diffusion D = σ²**: GFL provides stochastic exploration
- **Stationary ρ∞ ∝ exp(-V/D)**: Equilibrium when GFM-GFL balanced

## Practical Applications

### 1. Multi-Agent Coordination
```julia
# Three agents with GF(3) conservation
gfm = GridFormingAgent(...)     # :PLUS
gfl1 = GridFollowingAgent(...)  # :MINUS
gfl2 = GridFollowingAgent(...)  # :ERGODIC
# Σ = +1 - 1 + 0 = 0 ✓
```

### 2. Skill Dispersal
```julia
# Spectral gap controls how fast skills spread
gap = 0.25  # Optimal: skills reach all agents in 4τ
```

### 3. Proof Dependency Graphs
```julia
# From spectral_analyzer.jl
if gap >= 0.25
    :ramanujan  # Theorems well-connected
else
    :tangled    # Dependencies blocking mixing
end
```

## Files

- `~/Gay.jl/src/grid_coordination.jl` - Core framework
- `~/Gay.jl/examples/grid_coordination_demo.jl` - Interactive demo
- `~/Gay.jl/examples/fokker_planck.jl` - Underlying PDE
- `~/plurigrid-asi/ies/spectral_analyzer.jl` - Gap measurement

## Related Skills

- `fokker-planck` - The underlying PDE dynamics
- `spectral-analyzer` - Ramanujan gap measurement
- `gf3-coloring` - Triadic color assignment
- `bisimulation-game` - Agent equivalence via spectral properties

## Quick Reference

```
┌─────────────────────────────────────────────────────────┐
│  GRID COORDINATION CHEAT SHEET                         │
├─────────────────────────────────────────────────────────┤
│  GFM = Grid-Forming = Drift = Specification            │
│  GFL = Grid-Following = Diffusion = Direction Entropy  │
│                                                         │
│  Spectral Gap = λ₁ - λ₂                                │
│  Benchmark = 0.25 (Ramanujan)                          │
│  Mixing Time = 1/gap ≈ 4τ at benchmark                 │
│                                                         │
│  JUSTIFIED when: H(dir) ≈ S(spec) / 0.25              │
│                                                         │
│  GF(3): +:GFM-heavy  0:Balanced  -:GFL-heavy          │
└─────────────────────────────────────────────────────────┘
```

## GF(3) Assignment

- **Trit**: ERGODIC (0) - coordination/synthesis skill
- **Hue**: 120° (green) - balanced mixing dynamics
