# Self-Assignment Color Game: Occupancy Levels

## The Game

Agents self-assign to skills. Colors emerge from occupancy.

```
┌─────────────────────────────────────────────────────────────┐
│  OCCUPANCY LEVEL        │  COLOR   │  TRIT  │  DYNAMICS    │
├─────────────────────────┼──────────┼────────┼──────────────┤
│  many-to-none (M→∅)     │  RED     │  -1    │  contraction │
│  many-to-many (M→M)     │  GREEN   │   0    │  ergodic     │
│  many-to-more (M→M+)    │  BLUE    │  +1    │  expansion   │
└─────────────────────────┴──────────┴────────┴──────────────┘
```

## Rules

```julia
struct Agent
    id::Int
    color::Int  # -1, 0, +1
end

struct Skill
    name::String
    capacity::Int  # max agents
    occupants::Vector{Agent}
end

function occupancy_color(skill::Skill)
    n = length(skill.occupants)
    c = skill.capacity
    
    if n > c      # many-to-none: overflow → agents leave
        return -1  # RED: contraction
    elseif n == c # many-to-many: balanced
        return 0   # GREEN: ergodic
    else          # many-to-more: room for growth
        return +1  # BLUE: expansion
    end
end
```

## Self-Assignment Dynamics

```
Round t:
  1. Each agent observes skill colors
  2. Agent picks skill based on own trit:
     - RED agent (-1)  → seeks GREEN or BLUE skills (escape contraction)
     - GREEN agent (0) → stays put (ergodic)
     - BLUE agent (+1) → seeks RED skills (fill vacancies)
  3. Update occupancy → new colors emerge
  4. Repeat until GF(3) conservation: Σ colors = 0
```

## Example: 3 Agents, 3 Skills

```
Initial:
  Agents: A(-1), B(0), C(+1)
  Skills: LEVIN(cap=1), LEVITY(cap=1), ERGODIC(cap=1)

Round 0:
  All unassigned → all skills BLUE (+1)
  
Round 1:
  A(-1) → LEVIN   (seeks expansion)
  B(0)  → ERGODIC (stays central)
  C(+1) → LEVITY  (fills vacancy)
  
  Occupancy: LEVIN=1/1, LEVITY=1/1, ERGODIC=1/1
  Colors:    GREEN(0), GREEN(0), GREEN(0)
  Sum: 0 ✓ GF(3) CONSERVED

Round 2 (perturbation: new agent D(+1) arrives):
  D(+1) → wants RED skill (to fill)
  But all GREEN → D picks randomly → LEVIN
  
  Occupancy: LEVIN=2/1 (overflow!), LEVITY=1/1, ERGODIC=1/1
  Colors:    RED(-1), GREEN(0), GREEN(0)
  Sum: -1 ✗ NOT CONSERVED
  
Round 3 (rebalancing):
  A(-1) sees LEVIN is RED → leaves for BLUE skill
  But no BLUE skills exist → A creates new skill "CURIOSITY"
  
  Occupancy: LEVIN=1/1, LEVITY=1/1, ERGODIC=1/1, CURIOSITY=1/2
  Colors:    GREEN(0), GREEN(0), GREEN(0), BLUE(+1)
  Sum: +1 ✗ STILL NOT CONSERVED
  
Round 4:
  System spawns phantom agent P(-1) OR
  D(+1) leaves system (many-to-none)
  
  Final: Sum = 0 ✓
```

## Occupancy Transitions

```
         many-to-more (+1)
              │
              │ agents arrive
              ▼
         many-to-many (0) ◄──── equilibrium
              │
              │ agents overflow
              ▼
         many-to-none (-1)
              │
              │ agents leave
              ▼
         many-to-more (+1)
              
        ─────────────────────
        CYCLE PERIOD = 3 (mod GF(3))
```

## Julia Implementation

```julia
using Gay: fingerprint, trit

mutable struct OccupancyGame
    agents::Vector{Agent}
    skills::Vector{Skill}
    seed::UInt64
end

function step!(game::OccupancyGame)
    # Compute current colors
    colors = [occupancy_color(s) for s in game.skills]
    
    # Agents self-assign based on color matching
    for agent in game.agents
        current_skill = find_skill(game, agent)
        
        if agent.color == -1  # RED agent
            # Seek non-RED skill
            target = findfirst(c -> c >= 0, colors)
        elseif agent.color == +1  # BLUE agent
            # Seek RED skill (fill vacancy)
            target = findfirst(c -> c == -1, colors)
        else  # GREEN agent
            target = nothing  # stay put
        end
        
        if !isnothing(target)
            move!(agent, current_skill, game.skills[target])
        end
    end
    
    # Check GF(3) conservation
    new_colors = [occupancy_color(s) for s in game.skills]
    return sum(new_colors) % 3
end

function run_until_conserved!(game::OccupancyGame; max_rounds=100)
    for round in 1:max_rounds
        residual = step!(game)
        if residual == 0
            println("Converged at round $round")
            return round
        end
    end
    println("Did not converge")
    return -1
end
```

## Connection to Levin-Levity

| Occupancy | Levin-Levity Role | Fokker-Planck |
|-----------|-------------------|---------------|
| many-to-none | LEVIN overflow (too many provers on same approach) | Drift μ > 0 |
| many-to-many | Nash equilibrium (balanced allocation) | ∂P/∂t = 0 |
| many-to-more | LEVITY expansion (unexplored proof space) | Diffusion D > 0 |

## WEV from Occupancy Imbalance

```
WEV = |Σ occupancy_colors|

When WEV > 0:
  - System is out of GF(3) balance
  - Arbitrage opportunity exists
  - Agents can profit by self-reassigning

When WEV = 0:
  - Nash equilibrium achieved
  - No profitable deviation
  - Colors sum to zero
```

## Seed 1069 Example

```julia
game = OccupancyGame(seed=1069)

# Initialize with Levin-Levity triad
add_skill!(game, "busy-beaver-oracle", capacity=3, trit=+1)
add_skill!(game, "levin-levity", capacity=5, trit=0)
add_skill!(game, "prediction-market", capacity=2, trit=-1)

# Add agents from cognitive superposition
add_agent!(game, "Riehl", trit=-1)
add_agent!(game, "Sutskever", trit=+1)
add_agent!(game, "Schmidhuber", trit=+1)
add_agent!(game, "Bengio", trit=0)

# Run self-assignment
rounds = run_until_conserved!(game)
# → Converges when Riehl→prediction-market, 
#   Sutskever+Schmidhuber→busy-beaver-oracle,
#   Bengio→levin-levity
```

---

```
GF(3) CONSERVATION:
  (-1) + (0) + (+1) = 0
  RED + GREEN + BLUE = BLACK (absorbed)
  many-to-none + many-to-many + many-to-more = equilibrium
```
