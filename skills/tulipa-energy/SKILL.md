---
name: tulipa-energy
description: TulipaEnergyModel.jl — Julia energy system optimization for investment + operation decisions across electricity, hydrogen, heat, gas. Connects to glass-line RWA via geothermal bore modeling.
version: 1.0.0
metadata:
  trit: -1
  role: VALIDATOR
  color: "#2E8B57"
  language: julia
  repo: TulipaEnergy/TulipaEnergyModel.jl
  license: Apache-2.0
  stars: 65
  coworld: glass-line
---

# Tulipa Energy Model

Julia optimization model for energy system investment and operation decisions.

## Why This Matters

TulipaEnergyModel.jl optimizes across multiple energy sectors — electricity, hydrogen, heat, gas. The glass-line RWA (geothermal bore + fiber + compute at Plurigrid Portal, Portland) produces exactly these revenue streams. Tulipa can model:

- **GeoToken (g)**: geothermal electricity generation, dispatch optimization
- **ThermalToken (d)**: direct-use heating, district heating network
- **ComputeToken (c)**: compute powered by geothermal, load scheduling
- **LumenToken (b)**: fiber optic capacity allocation
- **BrineToken (n)**: mineral extraction from geothermal brine

The model determines optimal investment timing (when to drill, when to expand) and operation (how to dispatch across revenue streams each hour).

## Installation

```julia
using Pkg
Pkg.add("TulipaEnergyModel")
```

## Core Concepts

### Assets
- **Producer**: geothermal plant, solar array
- **Consumer**: compute load, district heating demand
- **Conversion**: heat → electricity (ORC), electricity → compute
- **Storage**: thermal storage, battery
- **Transport**: transmission lines, heat pipes, fiber

### Optimization
- Mixed-integer linear programming (MILP)
- Multi-period (hourly, daily, seasonal)
- Investment + operation co-optimization
- Uses HiGHS solver (open source)

## Usage for Glass-Line Modeling

```julia
using TulipaEnergyModel

# Define the geothermal bore as a Producer asset
# Portland Cascadia volcanic arc: 40-60°C/km gradient
# 2km bore → 80-120°C fluid temperature
# Binary ORC cycle → ~10% thermal-to-electric efficiency

# Model inputs:
# - Drilling cost: $5M-10M per bore
# - Thermal output: ~5 MWth continuous
# - Electric output: ~500 kWe (binary cycle)
# - Revenue: electricity + heat + compute + fiber + brine
# - DOE EGS grant: up to $25M match

# The optimization tells you:
# 1. When to invest (NPV maximizing drill date)
# 2. How to dispatch (hourly revenue allocation)
# 3. Break-even timeline (years to payback)
# 4. Optimal capacity sizing (bore depth, ORC rating)
```

## Integration with Allocator

The Move allocator's glass-line strategy (`TRIT_MINUS`, conservative/physical) reads its `observed_apy_bps` from a Tulipa model run:

```
Tulipa model run (offline, Julia)
  → annual revenue estimate ($/yr)
  → convert to APT at current price
  → set as observed_apy_bps in Move strategy
  → allocator rebalance() fold includes physical yield

This bridges continuous (DeFi) and discontinuous (physical) yield.
```

## Key Files

| File | Purpose |
|------|---------|
| `src/TulipaEnergyModel.jl` | Main module |
| `src/model.jl` | Optimization model formulation |
| `src/io.jl` | Data input/output |
| `docs/` | Full documentation |
| `benchmark/` | Performance benchmarks |

## References

- Repo: https://github.com/TulipaEnergy/TulipaEnergyModel.jl
- Docs: https://TulipaEnergy.github.io/TulipaEnergyModel.jl/stable/
- DOI: CITATION.cff in repo
- bmorphism starred this — connection to glass-line RWA thesis
- Related: worlds/g/rwa_manifest_destiny.md, gayfnox-allocator/
