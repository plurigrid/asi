# Energy Dynamics ACSet: IES Addon

Physics-motivated measurement and optimization for computational skill ecosystems.

## Quick Start

### 1. Load the Schema

```julia
using Catlab, ACSets
include("schema.jl")

# Create an empty acset
acset = EnergyDynamicsACSet()
```

### 2. Add Skills, Flows, and States

```julia
# Add GF(3) trits
minus_id = add_part!(acset, :Trit; trit_value=-1, trit_name="MINUS")
ergodic_id = add_part!(acset, :Trit; trit_value=0, trit_name="ERGODIC")
plus_id = add_part!(acset, :Trit; trit_value=+1, trit_name="PLUS")

# Add a skill
skill = add_part!(acset, :Skill;
    schema_complexity=5.7,
    representational_depth=7,
    storage_footprint=250_000,
    trit_assignment=ergodic_id
)

# Add energy flow through this skill
flow = add_part!(acset, :EnergyFlow;
    entropy_rate=0.15,
    interaction_degree=4,
    bandwidth_utilization=0.6,
    energy_source=skill,
    energy_sink=skill
)

# Add dynamical state
state = add_part!(acset, :DynamicalState;
    kinetic_energy=0.36,
    potential_energy=39.9,
    hamiltonian=40.26
)
```

### 3. Compute Energy Metrics

```julia
# Kinetic information energy
K = kinetic_information_energy(acset, flow)
# → 0.36

# Potential information energy
V = latent_potential_energy(acset, skill)
# → 39.9

# Total energy (should equal H)
H = total_energy(acset, state)
# → 40.26

# Energy density (bits/byte/sec)
density = energy_density(acset, skill)
# → 0.00144

# Check conservation
is_conserving = is_energy_conserving(acset, state)
# → true
```

### 4. Run Complete Example

```julia
acset = create_energy_dynamics_example()
energy_report(acset)
```

Output:
```
================================================================================
ENERGY DYNAMICS ACSet REPORT
================================================================================

▸ GF(3) TRIAD CONSERVATION:
  Σ trit = 0 (mod 3)
  ✓ Balanced: true

▸ KINETIC INFORMATION ENERGY (Interaction Entropy):
  Flow 1: 0.018 (from complexity=2.1 to 5.7)
  Flow 2: 0.36 (from complexity=5.7 to 8.3)
  Flow 3: 1.8 (from complexity=8.3 to 2.1)

▸ POTENTIAL INFORMATION ENERGY (Schema Capacity):
  Skill 1: capacity=6.3, storage=50.0KB
  Skill 2: capacity=39.9, storage=250.0KB
  Skill 3: capacity=99.6, storage=600.0KB

▸ DYNAMICAL STATES (Pendulum Oscillation):
  State 1: T=0.1, V=0.9, H=1.0, Conserved=true
  State 2: T=0.5, V=0.5, H=1.0, Conserved=true
  State 3: T=0.9, V=0.1, H=1.0, Conserved=true

▸ REACTION STRUCTURES (Hamiltonian Coupling):
  Reaction 1: T*Q=0.3, TQ=0.7, rate=0.2
  Reaction 2: T*Q=0.5, TQ=0.5, rate=0.5
  Reaction 3: T*Q=0.7, TQ=0.3, rate=0.8

================================================================================
```

## Core Concepts

### Kinetic Energy (K)
Current interaction rate: entropy_rate × interaction_degree × bandwidth_utilization
- Measures active, boundary dissipation
- High K: skill is in heavy use
- Low K: skill is latent

### Potential Energy (V)
Stored schema richness: schema_complexity × representational_depth
- Measures representational capacity
- High V: rich, diverse, future-capable
- Low V: simple, specialized

### Hamiltonian (H = T + V)
Total energy, conserved along trajectories
- Skills oscillate: latent (high V) ↔ active (high K)
- H is invariant even as T and V exchange

### Reaction Rate (α)
Coupling strength between latent and active modes
- High α: fast oscillation, responsive to load
- Low α: slow oscillation, sluggish response

### Energy Density
Efficiency metric: kinetic_energy / storage_footprint
- High density: prioritize for deployment
- Low density: defer or optimize

### GF(3) Trits
Triadic balance for ecosystem scheduling
- PLUS (+1): generative, high energy density
- ERGODIC (0): coordinating, moderate density
- MINUS (-1): dissipative, low density
- Conservation: Σ trit ≡ 0 (mod 3)

## Theory

For detailed mathematical foundations, see:

- **THEORY.md**: Complete integration of Patterson (ACSet theory), Capucci (open energy-driven systems), and Libkind (dynamical systems)
- **SKILL.md**: Full documentation of schema, functions, and Plurigrid ASI integration plan

## Key Functions

| Function | Purpose |
|----------|---------|
| `kinetic_information_energy(acset, flow_id)` | K = entropy_rate × degree × bandwidth |
| `latent_potential_energy(acset, skill_id)` | V = complexity × depth |
| `total_energy(acset, state_id)` | H = T + V |
| `energy_density(acset, skill_id)` | K / storage_footprint |
| `is_energy_conserving(acset, state_id)` | Verify H = T + V |
| `gf3_conservation(acset)` | Verify Σ trit ≡ 0 (mod 3) |
| `hamiltonian_dynamics_step(acset, state_id, dt)` | Symplectic integration |
| `pendulum_trajectory(acset, skill_id, range)` | Generate phase space trajectory |
| `create_energy_dynamics_example()` | Create 3-skill example system |
| `energy_report(acset)` | Print comprehensive report |

## Plurigrid ASI Integration (491 Skills)

### Next Steps

1. **Extract Metrics** from `gh_acset_export.json`
   - entropy_rate from commit/PR velocity
   - interaction_degree from concurrent contributors
   - schema_complexity from codebase metrics
   - representational_depth from ACSet nesting

2. **Compute Energies** for all 491 skills
   - Run kinetic/potential energy pipeline
   - Verify Hamiltonian conservation
   - Create energy histograms

3. **Assign Triads** by energy density
   - Sort skills
   - Assign PLUS/ERGODIC/MINUS roles
   - Verify GF(3) balance

4. **Optimize Scheduling**
   - Deploy high-density skills first
   - Maintain triadic equilibrium
   - Monitor oscillation periods

## File Structure

```
energy-dynamics-acset/
├── README.md           # This file (quick start)
├── SKILL.md           # Full documentation
├── THEORY.md          # Mathematical integration
└── schema.jl          # Formal ACSet schema + functions
```

## Mathematics

### Schema
```
Skill --reaction→ ReactionStructure
  ↓
current_state
  ↓
DynamicalState ← next_state ← DynamicalState
  ↓
time_step
  ↓
TimePoint

EnergyFlow
  ├→ energy_source → Skill
  └→ energy_sink   → Skill
```

### Energy Dynamics
```
dT/dt = α(V - T)     (kinetic ← potential)
dV/dt = α(T - V)     (potential ← kinetic)
d(H)/dt = 0          (total energy invariant)
```

### GF(3) Conservation
```
Σ trit_value ≡ 0 (mod 3)
```

## References

- Patterson, E., Lynch, O., & Fairbanks, J. (2022). "Categorical Data Structures for Technical Computing." arXiv:2106.04703v5
- Capucci, M. (2024). "Organizing Physics with Open Energy-Driven Systems." arXiv:2404.16140
- Libkind, S. (2024+). Dynamical Systems Composition and Pendulum Dynamics. https://slibkind.github.io/

## Status

- ✓ Formal schema complete (Patterson notation)
- ✓ Capucci reaction structures integrated
- ✓ Libkind pendulum dynamics implemented
- ✓ GF(3) triadic organization
- [ ] Plurigrid ASI metrics extraction
- [ ] Energy computation for 491 skills
- [ ] Triadic scheduling optimization

**Generated**: 2026-01-01
