# Energy for Reachability in ALife Systems

How different ALife repositories implement **energy as the cost of state reachability**.

## The ⊛ Energy Principle

```
Reachable(S') = { S' : E_barrier(S → S') ≤ E_budget(P) }

where:
  - P = parameters (agent's controllable degrees of freedom)
  - S = current state
  - S' = target state
  - E_barrier = energy cost to reach S' from S
  - E_budget = energy available to the agent
  - ⊛ = agency operator that transduces P into state change
```

---

## ALIEN (chrxh/alien)

**Model**: Explicit particle energy budgets

### Energy Sources
- Radiation sources in environment
- Consumption of other organisms
- Energy transfer between cells

### Energy Costs
| Action | Energy Cost |
|--------|-------------|
| Movement | Proportional to mass × velocity change |
| Cell division | Fixed cost per new cell |
| Neural firing | Small fixed cost |
| Weapon discharge | Large burst cost |
| Construction | Proportional to complexity |

### Reachability Implication
```cpp
// From ALIEN source
struct Cell {
    float energy;
    float maxEnergy;

    bool canPerformAction(ActionType action) {
        return energy >= actionCost(action);
    }

    void performAction(ActionType action) {
        energy -= actionCost(action);
        // State transition via ⊛
    }
};
```

**Key Insight**: Creatures with more energy can reach more states (larger reachable set). Starvation shrinks reachability to survival-only behaviors.

---

## Particle Lenia (Google Research)

**Model**: Energy-based field formulation

### Energy Function
```python
# Total energy of particle configuration
def energy(positions, params):
    # Pairwise interaction energy
    E_interaction = sum(
        U(distance(p_i, p_j), params)
        for i, j in pairs(positions)
    )
    # Self-energy (prevents collapse)
    E_self = sum(sigma(p) for p in positions)
    return E_interaction + E_self

# Dynamics = gradient descent on energy
def step(positions, params):
    grad_E = gradient(energy, positions)
    return positions - dt * grad_E
```

### Reachability
States are reachable if they're in the **basin of attraction** of an energy minimum:

```
Reachable(S') iff ∃ path: E(path) is monotonically decreasing to S'
```

**Key Insight**: Local minima create "attractors" - stable configurations the system naturally reaches.

---

## Flow-Lenia (Mass Conservation)

**Model**: Energy via mass conservation

### Conservation Law
```latex
∂A/∂t + ∇·(A·v) = 0

% No mass created or destroyed
% "Energy" = total mass in region
```

### Flow-Based Reachability
```python
def flow_lenia_step(A, kernel, params):
    # Compute flow field from local interactions
    v = compute_velocity_field(A, kernel)

    # Mass-conserving update
    # States reachable = those connected by divergence-free flow
    A_new = A - dt * divergence(A * v)

    return A_new
```

**Key Insight**: Reachability constrained by what mass flows can achieve. Some configurations unreachable without "importing" mass from elsewhere.

---

## Sensorimotor Lenia (Agency)

**Model**: Self-maintenance as energy budget

### Three Capacities
| Capacity | Energy Cost | Reachability Effect |
|----------|-------------|---------------------|
| **Individuality** | Maintaining boundary | Preserves reachable set |
| **Self-maintenance** | Homeostatic regulation | Keeps system near attractor |
| **Sensori-motricity** | Sensing + acting | Expands reachable set |

### Agent Energy Budget
```python
class SensorimotorAgent:
    def __init__(self):
        self.individuality_cost = 0.1   # Per timestep
        self.sensing_cost = 0.05        # Per observation
        self.action_cost = 0.2          # Per motor command

    def reachable_set(self, energy_budget):
        """States reachable given energy budget."""
        # More energy → more sensing → better knowledge of environment
        # More energy → more actions → more state transitions

        max_actions = energy_budget // self.action_cost
        max_sensing = energy_budget // self.sensing_cost

        return expand_reachability(
            self.current_state,
            n_actions=max_actions,
            n_observations=max_sensing
        )
```

---

## Neural Cellular Automata (Growing NCA)

**Model**: Implicit energy via stochastic masking

### Update Rule
```python
def nca_step(grid, model):
    # Not all cells update every step
    # "Energy" = probability of being active

    perception = perceive(grid)
    delta = model(perception)

    # Stochastic cell update (fire_rate = "energy")
    mask = random() < fire_rate  # 0.5 typical

    return grid + delta * mask
```

### Reachability Implication
- **High fire_rate**: More cells active → faster dynamics → larger reachable set per timestep
- **Low fire_rate**: Fewer active → slower → more constrained reachability

---

## JaxLife (Open-Ended Agentic)

**Model**: Explicit energy metabolism + Turing-complete robots

### Energy Flow
```python
class JaxLifeWorld:
    # Energy sources
    terrain_energy: Array  # Varies spatially

    # Agents have metabolism
    class Agent:
        energy: float
        metabolism_rate: float  # Energy consumed per step

        def can_act(self, action):
            return self.energy >= action.cost

        def step(self):
            self.energy -= self.metabolism_rate
            if self.energy <= 0:
                self.die()
```

### Turing-Complete Reachability
Agents can program **robots** that perform Turing-complete computation:
- Robots extend agent's reachable set
- Programming cost vs. execution benefit tradeoff
- Robots as "agency amplifiers"

---

## Comparison: Energy Models

| System | Energy Type | Conservation | Reachability |
|--------|-------------|--------------|--------------|
| **ALIEN** | Explicit tokens | Locally conserved | Action budget |
| **Particle Lenia** | Field potential | Global minimum | Basin of attraction |
| **Flow-Lenia** | Mass | Strictly conserved | Flow-connected |
| **Sensorimotor Lenia** | Agent budget | Dissipative | Sensing + acting |
| **NCA** | Fire probability | Stochastic | Update frequency |
| **JaxLife** | Metabolism | Dissipative | Agent + robot |

---

## ⊛ Unifies All Models

```
┌─────────────────────────────────────────────────────────────┐
│                     P (parameters)                          │
│              ┌──────────────────────────┐                   │
│              │  • ALIEN: cell genome    │                   │
│              │  • Lenia: kernel params  │                   │
│              │  • NCA: neural weights   │                   │
│              │  • JaxLife: agent policy │                   │
│              └───────────┬──────────────┘                   │
│                          │                                  │
│                          │ ⊛ (agency)                       │
│                          │                                  │
│                          ▼                                  │
│              ┌──────────────────────────┐                   │
│              │  S (state)               │                   │
│              │  • Particle positions    │                   │
│              │  • Field values          │                   │
│              │  • Grid cells            │                   │
│              └───────────┬──────────────┘                   │
│                          │                                  │
│                          │ E_cost(S → S')                   │
│                          │                                  │
│                          ▼                                  │
│              ┌──────────────────────────┐                   │
│              │  S' ∈ Reachable(P, E)    │                   │
│              │  iff E_cost ≤ E_budget   │                   │
│              └──────────────────────────┘                   │
└─────────────────────────────────────────────────────────────┘
```

---

## Spectral Gap Connection

The **spectral gap** (λ = 1/4 Ramanujan bound) determines mixing time:

```
τ_mix ∝ 1/λ

Large gap → fast mixing → all states quickly reachable
Small gap → slow mixing → states segregated into "energy wells"
```

For ALife systems:
- **High spectral gap**: Adaptable organisms, can reach diverse phenotypes
- **Low spectral gap**: Specialized organisms, trapped in niches

---

## Implementation Pattern

```julia
# Universal energy-for-reachability interface
abstract type EnergyModel end

struct ReachabilityQuery
    source::State
    target::State
    energy_budget::Float64
end

function is_reachable(model::EnergyModel, query::ReachabilityQuery)::Bool
    cost = transition_cost(model, query.source, query.target)
    return cost ≤ query.energy_budget
end

function reachable_set(model::EnergyModel, source::State, budget::Float64)::Set{State}
    # BFS/Dijkstra over state space with energy as edge weights
    return states_within_cost(model, source, budget)
end

# Specific implementations
struct ALIENEnergy <: EnergyModel
    action_costs::Dict{Symbol, Float64}
end

struct LeniaEnergy <: EnergyModel
    potential::Function  # U(r, params)
end

struct FlowLeniaEnergy <: EnergyModel
    # Mass-conserving: reachability = flow-connected
end
```

---

## Gay.jl Integration

```julia
using Gay

# Color-code reachability regions
gay_seed!(0x454E5247)  # "ENRG"

ENERGY_COLORS = Dict(
    :high_energy    => color_at(1),  # Hot
    :medium_energy  => color_at(2),  # Warm
    :low_energy     => color_at(3),  # Cool
    :unreachable    => color_at(4),  # Gray
)

function visualize_reachability(model, source, budget)
    for state in state_space(model)
        cost = transition_cost(model, source, state)
        if cost ≤ budget
            color = interpolate_color(
                ENERGY_COLORS[:high_energy],
                ENERGY_COLORS[:low_energy],
                cost / budget
            )
        else
            color = ENERGY_COLORS[:unreachable]
        end
        draw(state, color)
    end
end
```

---

**File**: `~/.claude/skills/truealife/ENERGY.md`
**Related**: SKILL.md, REPOS_2025.md, parametrised-optics-cybernetics
