---
name: nuclear-smr
description: Small Modular Reactor integration for Plurigrid energy dominance. Bridges neutronics simulation (OpenMC/MOOSE), categorical databases (ACSets), and on-chain coordination (Aptos).
---
# Nuclear SMR Skill

> **Trit: +1 (GENERATOR)**

## Overview

Small Modular Reactor integration for Plurigrid energy dominance. Bridges neutronics simulation (OpenMC/MOOSE), categorical databases (ACSets), and on-chain coordination (Aptos).

## When to Use

- SMR simulation and safety analysis
- Mesh generation for finite element multiphysics
- Monte Carlo neutronics with deterministic coloring
- Grid dispatch optimization for hybrid energy systems

## Plurigrid SMR Dominance Stack

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    LAYER 1: SIMULATION                                   │
├─────────────────────────────────────────────────────────────────────────┤
│  idaholab/moose (1.7K⭐) → Finite element multiphysics                  │
│  openmc-dev/openmc (931⭐) → Monte Carlo neutronics                     │
│  stellarmesh (66⭐) → Mesh generation for FEM                           │
│  ↓                                                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                    LAYER 2: CATEGORICAL DATABASE                         │
├─────────────────────────────────────────────────────────────────────────┤
│  ACSets.jl → Mesh as attributed C-set                                   │
│  StructuredDecompositions.jl → Sheaves on tree decompositions           │
│  DuckDB → Time-travel queries on simulation runs                        │
│  ↓                                                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                    LAYER 3: ON-CHAIN COORDINATION                        │
├─────────────────────────────────────────────────────────────────────────┤
│  society.move → Operator registry, safety attestations                  │
│  multiverse_v3.move → 3 parallel bifurcation slots (MINUS/ERG/PLUS)     │
│  hyperbolic_bulk.move → GF(3) entropy storage                           │
│  ↓                                                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                    LAYER 4: GRID DISPATCH                                │
├─────────────────────────────────────────────────────────────────────────┤
│  idaholab/HERON → Hybrid energy systems optimization                    │
│  Load following: SMR + solar/wind hybrid                                │
│  Microgrids: Developing world remote deployment                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## Key Repositories

| Repository | Stars | Purpose | GF(3) Mapping |
|------------|-------|---------|---------------|
| `idaholab/moose` | 1.7K | Multiphysics FEM | +1 Generator |
| `openmc-dev/openmc` | 931 | Monte Carlo neutronics | +1 Generator |
| `stellarmesh` | 66 | Mesh generation | 0 Coordinator |
| `idaholab/HERON` | - | Hybrid systems | -1 Validator |

## SMR Advantages for Developing World

1. **Factory-built**: Ship assembled, reduce on-site complexity
2. **Passive safety**: No external power needed for shutdown (valence = +3)
3. **Load-following**: Complement variable renewables
4. **Smaller upfront capital**: $1-3B vs $10B+ for traditional
5. **Co-generation**: District heating + desalination

## QRI Valence Integration

Grid states mapped to XY model topology for bankable assets:

| Grid State | Valence | Vortices | Action |
|------------|---------|----------|--------|
| Blackout | -3 | many | emergency-withdraw |
| Brownout | -2 | some | gradual-withdraw |
| Unstable | -1 | few | hold-cautious |
| Balanced | 0 | none | hold |
| Surplus | +1 | annihilating | hold-growth |
| Export-ready | +2 | none | deposit |
| Dominant | +3 | none | deposit-compound |

## Commands

```bash
# OpenMC simulation with Gay.jl coloring
julia --project=. -e 'using OpenMC, Gay; run_simulation(seed=137508)'

# Mesh → ACSet conversion
julia -e 'using ACSets, StellaMesh; mesh_to_acset(load_mesh("reactor.msh"))'

# Deploy SMR operator registry
aptos move publish --package-dir wev_move_contracts --named-addresses wev=default

# HERON optimization
python -m heron --input smr_hybrid_config.yaml
```

## Related Skills

| Skill | Trit | Bridge |
|-------|------|--------|
| `energy-dominance` | +1 | Policy framework |
| `gay-mcp` | +1 | Monte Carlo coloring |
| `acsets` | 0 | Mesh topology |
| `goblins` | 0 | Distributed operators |
| `aptos-gf3-society` | +1 | On-chain safety |
| `qri-valence` | 0 | XY model topology |
| `intent-sink` | -1 | Demand absorption |

## Triad Conservation

```
nuclear-smr (+1) + acsets (0) + intent-sink (-1) = 0 ✓
```

## References

- [NUCLEAR_SMR_REPOSITORIES.md](file:///Users/bob/ies/NUCLEAR_SMR_REPOSITORIES.md)
- [PLURIGRID_ENERGY_DOMINANCE_AGENDA.md](file:///Users/bob/ies/PLURIGRID_ENERGY_DOMINANCE_AGENDA.md)
- [multiverse_v3.move](file:///Users/bob/ies/wev_move_contracts/sources/multiverse_v3.move)
- [OpenMC Documentation](https://docs.openmc.org/)
- [MOOSE Framework](https://mooseframework.inl.gov/)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
