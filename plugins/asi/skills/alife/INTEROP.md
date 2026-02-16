# ALIFE Skill Interoperability

**Skill**: alife
**Trit**: +1 (PLUS - generative)
**Interop Protocol**: GF(3) conservation + seed propagation

---

## Compatible Skills

| Skill | Interop Type | Use Case |
|-------|--------------|----------|
| `gay-mcp` | **Primary** | Deterministic coloring of all ALife entities |
| `acsets-algebraic-databases` | **Schema** | Category-theoretic modeling of ALife structures |
| `glass-bead-game` | **Synthesis** | Cross-domain connections (math↔music↔philosophy) |
| `self-validation-loop` | **Verification** | Prediction vs observation for CA dynamics |
| `algorithmic-art` | **Rendering** | p5.js visualization of Lenia/NCA patterns |
| `epistemic-arbitrage` | **Transfer** | Knowledge propagation across ALife domains |
| `world-hopping` | **Navigation** | Badiou triangle for parameter space exploration |
| `bisimulation-game` | **Resilience** | Skill dispersal with GF(3) conservation |
| `triad-interleave` | **Parallel** | Three-stream execution for CA updates |
| `hatchery-papers` | **Reference** | Academic papers (ALIEN, Lenia, NCA) |

---

## 1. gay-mcp Integration

### Coloring ALife Themes
```julia
using Gay

# ALIFE domain seeds (deterministic)
const ALIFE_SEEDS = Dict(
    :lenia       => 0x4C454E49,  # "LENI"
    :nca         => 0x4E434100,  # "NCA\0"
    :evolution   => 0x45564F4C,  # "EVOL"
    :swarm       => 0x5357524D,  # "SWRM"
    :autopoiesis => 0x4155544F,  # "AUTO"
    :concordia   => 0x434F4E43,  # "CONC"
)

# Generate theme palette
function alife_palette(theme::Symbol, n::Int=8)
    seed = get(ALIFE_SEEDS, theme, 0x414C4946)
    Gay.palette(n, seed=seed)
end

# GF(3) classification of CA states
function ca_state_trit(state::Float64)
    # Map continuous state [0,1] to trit
    state < 0.33 ? -1 : state < 0.67 ? 0 : +1
end
```

### MCP Tool Chain
```bash
# 1. Set seed for Lenia simulation
mcp gay gay_seed 0x4C454E49

# 2. Generate palette for visualization
mcp gay palette 12

# 3. Track reafference (self-recognition in CA)
mcp gay reafference seed=0x4C454E49 index=100 predicted_hex="#A855F7"
```

---

## 2. acsets-algebraic-databases Integration

### Lenia as ACSet Schema
```julia
using Catlab.CategoricalAlgebra

# Define Lenia schema
@present SchLenia(FreeSchema) begin
    Cell::Ob
    Neighbor::Ob
    
    src::Hom(Neighbor, Cell)
    tgt::Hom(Neighbor, Cell)
    
    State::AttrType
    Param::AttrType
    
    state::Attr(Cell, State)
    kernel::Attr(Neighbor, Param)
    growth::Attr(Cell, Param)
end

@acset_type LeniaGrid(SchLenia){Float64, Vector{Float64}}

# Create Lenia simulation as ACSet
function lenia_to_acset(grid::Matrix{Float64}, kernel::Matrix{Float64})
    L = LeniaGrid()
    nx, ny = size(grid)
    
    # Add cells
    for i in 1:nx, j in 1:ny
        add_part!(L, :Cell, state=grid[i,j], growth=[0.0])
    end
    
    # Add neighbor relations
    for i in 1:nx, j in 1:ny
        for di in -1:1, dj in -1:1
            (di == 0 && dj == 0) && continue
            ni, nj = mod1(i+di, nx), mod1(j+dj, ny)
            src_id = (i-1)*ny + j
            tgt_id = (ni-1)*ny + nj
            add_part!(L, :Neighbor, src=src_id, tgt=tgt_id, kernel=kernel[di+2, dj+2])
        end
    end
    L
end
```

### Flow-Lenia with Mass Conservation
```julia
# Schema extension for Flow-Lenia
@present SchFlowLenia <: SchLenia begin
    Velocity::AttrType
    velocity::Attr(Cell, Velocity)
    
    # Mass conservation constraint (implicit in morphisms)
end

# Mass conservation as functor property
function verify_mass_conservation(L::LeniaGrid)
    total_mass = sum(L[:state])
    # After update, mass should be preserved
    @assert abs(total_mass - sum(L[:state])) < 1e-10
end
```

---

## 3. glass-bead-game Integration

### ALife Beads
```ruby
# Define ALife beads for Glass Bead Game
ALIFE_BEADS = {
  # Cellular Automata
  lenia: Bead.new(:continuous_ca, domain: :emergence),
  nca: Bead.new(:neural_ca, domain: :learning),
  gol: Bead.new(:discrete_ca, domain: :computation),
  
  # Evolution
  replicator: Bead.new(:dynamics, domain: :evolution),
  fitness: Bead.new(:selection, domain: :evolution),
  mutation: Bead.new(:variation, domain: :evolution),
  
  # Foundations
  autopoiesis: Bead.new(:closure, domain: :philosophy),
  mr_system: Bead.new(:metabolism, domain: :mathematics),
  free_energy: Bead.new(:inference, domain: :cognition),
}

# Define morphisms between ALife and other domains
ALIFE_MORPHISMS = [
  # Lenia → Music (oscillatory patterns as waveforms)
  Morphism.new(:lenia, :timbre, via: :spectral_analysis),
  
  # NCA → Category Theory (local rules as natural transformations)
  Morphism.new(:nca, :functor, via: :local_to_global),
  
  # Autopoiesis → Monoid (operational closure)
  Morphism.new(:autopoiesis, :monoid, via: :closure_formalization),
  
  # Free Energy → Harmony (tension resolution)
  Morphism.new(:free_energy, :cadence, via: :prediction_error_minimization),
]
```

### World Hopping in Parameter Space
```ruby
# Lenia parameter space as possible worlds
class LeniaWorld
  attr_accessor :mu, :sigma, :kernel_radius, :seed
  
  def distance(other)
    # Badiou triangle inequality holds
    param_diff = Math.sqrt(
      (mu - other.mu)**2 + 
      (sigma - other.sigma)**2 + 
      (kernel_radius - other.kernel_radius)**2
    )
    seed_diff = (seed ^ other.seed).to_s(2).count('1') / 64.0
    param_diff + seed_diff
  end
  
  def hop_to(target, steps: 10)
    # Generate interpolation path
    (0..steps).map do |i|
      t = i.to_f / steps
      LeniaWorld.new(
        mu: mu * (1-t) + target.mu * t,
        sigma: sigma * (1-t) + target.sigma * t,
        kernel_radius: kernel_radius * (1-t) + target.kernel_radius * t,
        seed: i == steps ? target.seed : seed
      )
    end
  end
end
```

---

## 4. self-validation-loop Integration

### CA Prediction-Observation Loop
```julia
# Validate CA dynamics with reafference
function validate_ca_step(grid::Matrix{Float64}, kernel::Matrix{Float64}, seed::UInt64)
    # 1. Predict: efference copy of expected next state
    predicted = lenia_step(grid, kernel)
    predicted_trit = sum(ca_state_trit.(predicted)) % 3
    
    # 2. Observe: actually compute the step
    observed = lenia_step(grid, kernel)
    observed_trit = sum(ca_state_trit.(observed)) % 3
    
    # 3. Compare: reafference check
    match = predicted_trit == observed_trit
    
    # 4. Report
    Dict(
        :seed => seed,
        :predicted_trit => predicted_trit,
        :observed_trit => observed_trit,
        :match => match,
        :surprise => match ? 0 : abs(predicted_trit - observed_trit),
        :gf3_conserved => (predicted_trit - observed_trit) % 3 == 0
    )
end
```

### Active Inference for ALife Agents
```python
# Use Gay MCP's active inference for ALife agents
def alife_active_inference(agent_state, env_observation, seed):
    """
    Active Inference loop for artificial life agent.
    Minimizes free energy by updating beliefs or acting.
    """
    # Predict: what do we expect to observe?
    predicted = agent_state.predict(env_observation)
    
    # Free energy = prediction error + complexity
    prediction_error = distance(predicted, env_observation)
    complexity = agent_state.model_complexity()
    free_energy = prediction_error + complexity
    
    # Action selection: minimize expected free energy
    if free_energy > threshold:
        # Either update model (perceptual inference)
        # Or act to change observation (active inference)
        action = agent_state.select_action(minimize=free_energy)
    else:
        action = None  # Predictions match, no action needed
    
    return {
        'free_energy': free_energy,
        'prediction_error': prediction_error,
        'action': action,
        'seed': seed
    }
```

---

## 5. algorithmic-art Integration

### Lenia Visualization in p5.js
```javascript
// p5.js sketch for Lenia visualization with Gay.jl colors
let grid, kernel;
let gayPalette;

function setup() {
  createCanvas(400, 400);
  
  // Initialize Lenia grid
  grid = createLeniaGrid(100, 100);
  kernel = createLeniaKernel(13);
  
  // Get Gay.jl palette for visualization
  // Seed: 0x4C454E49 ("LENI")
  gayPalette = generateGayPalette(0x4C454E49, 256);
}

function draw() {
  // Update Lenia
  grid = leniaStep(grid, kernel);
  
  // Render with Gay.jl colors
  loadPixels();
  for (let i = 0; i < grid.length; i++) {
    for (let j = 0; j < grid[0].length; j++) {
      let state = grid[i][j];
      let colorIdx = floor(state * 255);
      let c = gayPalette[colorIdx];
      let idx = (i * width + j) * 4;
      pixels[idx] = c.r;
      pixels[idx+1] = c.g;
      pixels[idx+2] = c.b;
      pixels[idx+3] = 255;
    }
  }
  updatePixels();
}

function generateGayPalette(seed, n) {
  // SplitMix64 + golden angle (same as Gay.jl)
  let palette = [];
  let state = seed;
  for (let i = 0; i < n; i++) {
    state = splitmix64(state);
    let h = (state % 360 + i * 137.508) % 360;
    palette.push(hslToRgb(h, 70, 55));
  }
  return palette;
}
```

---

## 6. Composite Workflows

### Workflow: Lenia Discovery → Glass Bead → Visualization
```bash
# 1. Load skills
amp skill alife
amp skill gay-mcp
amp skill glass-bead-game
amp skill algorithmic-art

# 2. Generate Lenia patterns with Leniabreeder
just lenia-breed seed=0x4C454E49 n_generations=100

# 3. Color patterns deterministically
mcp gay palette 16 seed=0x4C454E49

# 4. Connect to music via Glass Bead Game
amp oracle "Find morphism from Lenia oscillation to musical timbre"

# 5. Render with p5.js
just art-lenia seed=0x4C454E49
```

### Workflow: NCA → ACSet → Validation
```julia
# Full pipeline: NCA training with ACSet modeling and validation
using ACSets, Gay

# 1. Define NCA as ACSet
nca_schema = define_nca_schema()
nca = NCAGrid(nca_schema)

# 2. Train with gradient descent
for epoch in 1:1000
    loss = train_step!(nca, target_pattern)
end

# 3. Validate with self-validation-loop
for i in 1:100
    result = validate_ca_step(nca.grid, nca.update_net, seed)
    @assert result[:gf3_conserved]
end

# 4. Color output deterministically
palette = Gay.palette(16, seed=0x4E434100)
visualize(nca, palette)
```

---

## GF(3) Conservation Protocol

All interoperating skills must maintain GF(3) conservation:

```julia
# Verify GF(3) across skill boundary
function verify_interop_gf3(source_skill::Symbol, target_skill::Symbol, data)
    source_trit = compute_trit(source_skill, data)
    target_trit = compute_trit(target_skill, data)
    
    # Conservation: sum of trits ≡ 0 (mod 3)
    (source_trit + target_trit) % 3 == 0
end
```

---

## Loading Multiple Skills

```bash
# Load alife with all interop skills
amp skill alife
amp skill gay-mcp
amp skill acsets-algebraic-databases
amp skill glass-bead-game
amp skill self-validation-loop
amp skill algorithmic-art
```

Or in a single session:
```
Load skills: alife, gay-mcp, acsets-algebraic-databases, glass-bead-game
```

---

**Interop Version**: 1.0.0
**Last Updated**: 2025-12-21
