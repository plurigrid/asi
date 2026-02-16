---
name: catalyst-chemical
description: Chemical reaction network modeling with Catalyst.jl. Autopoietic systems,
  unit-aware ODEs, and interacting subsystems.
source: SciML/Catalyst.jl + GitHub issues research
license: MIT
gf3_category: ZERO
---

# Catalyst Chemical Computing Skill

> **Addresses**: [Catalyst.jl #1341](https://github.com/SciML/Catalyst.jl/issues/1341) (DynamicQuantities units), [#1336](https://github.com/SciML/Catalyst.jl/issues/1336) (interacting subsystems)

## What is Catalyst.jl?

Catalyst.jl is a **symbolic modeling package for chemical reaction networks (CRNs)**. It enables:

- Declarative DSL for reaction systems
- Automatic conversion to ODEs, SDEs, jump processes
- Hierarchical composition of reaction networks
- Integration with ModelingToolkit.jl ecosystem

## Core Syntax

```julia
using Catalyst

# Define a simple reaction network
rn = @reaction_network begin
    k1, A + B --> C       # A + B → C with rate k1
    k2, C --> A + B       # C → A + B with rate k2
    k3, C --> D           # C → D with rate k3
end

# Convert to ODE system
osys = convert(ODESystem, rn)

# Solve
using DifferentialEquations
u0 = [:A => 1.0, :B => 1.0, :C => 0.0, :D => 0.0]
ps = [:k1 => 1.0, :k2 => 0.5, :k3 => 0.1]
tspan = (0.0, 10.0)
prob = ODEProblem(rn, u0, tspan, ps)
sol = solve(prob, Tsit5())
```

## Interacting Subsystems (Issue #1336)

Pattern for coupling reaction networks through observables:

```julia
using Catalyst, ModelingToolkit

# Subsystem 1: Gene expression
@reaction_network gene_expr begin
    @parameters α β
    @species mRNA(t) Protein(t)
    
    α, ∅ --> mRNA           # Transcription
    β, mRNA --> mRNA + Protein  # Translation
    1.0, mRNA --> ∅         # mRNA decay
    0.1, Protein --> ∅      # Protein decay
end

# Subsystem 2: Metabolic network (depends on Protein from subsystem 1)
@reaction_network metabolism begin
    @parameters v_max K_m
    @species Substrate(t) Product(t)
    
    # Michaelis-Menten kinetics with enzyme = Protein
    (v_max * Protein * Substrate) / (K_m + Substrate), Substrate --> Product
    0.05, Product --> ∅
end

# Compose via shared variable
function compose_systems(gene::ReactionSystem, metab::ReactionSystem)
    # Connect Protein from gene_expr to metabolism
    @named coupled = compose(gene, metab)
    
    # Add coupling equation: Protein in metabolism = Protein in gene_expr
    eqs = [metab.Protein ~ gene.Protein]
    
    extend(coupled, eqs)
end

coupled_system = compose_systems(gene_expr, metabolism)
```

## DynamicQuantities Integration (Issue #1341)

Unit-aware reaction modeling:

```julia
using Catalyst, DynamicQuantities

# Define units
const mM = u"mmol/L"
const s⁻¹ = u"s^-1"
const mM_s⁻¹ = u"mmol/L/s"

# Reaction network with units
rn_units = @reaction_network begin
    @parameters k1::typeof(1.0mM_s⁻¹) k2::typeof(1.0s⁻¹)
    @species A(t)::typeof(1.0mM) B(t)::typeof(1.0mM)
    
    k1, ∅ --> A      # Zero-order production
    k2, A --> B      # First-order conversion
end

# Solve with unit-aware initial conditions
u0_units = [:A => 1.0mM, :B => 0.0mM]
ps_units = [:k1 => 0.1mM_s⁻¹, :k2 => 0.05s⁻¹]
tspan_units = (0.0u"s", 100.0u"s")

# Note: Full unit propagation through ODE solve is WIP
```

## Autopoietic Closure Detection

Identify self-maintaining organizations in CRNs:

```julia
"""
Check if a set of species forms an autopoietic organization.

An organization is autopoietic if:
1. It is closed under the reaction network (all products are in the set)
2. It is self-maintaining (can regenerate all consumed species)
"""
function is_autopoietic(rn::ReactionSystem, species_set::Set{Symbol})
    reactions = Catalyst.reactions(rn)
    
    # Check closure: all products must be in set
    for rx in reactions
        # Check if any reactant is in our set
        reactant_syms = [Symbol(sp) for sp in rx.substrates]
        if !isempty(intersect(reactant_syms, species_set))
            # Then all products must also be in set
            product_syms = [Symbol(sp) for sp in rx.products]
            if !issubset(product_syms, species_set)
                return false
            end
        end
    end
    
    # Check self-maintenance: each species can be produced
    for sp in species_set
        can_produce = false
        for rx in reactions
            if Symbol(sp) in [Symbol(p) for p in rx.products]
                can_produce = true
                break
            end
        end
        if !can_produce
            return false
        end
    end
    
    return true
end

# Example: check if {A, B, C} is autopoietic
species = Set([:A, :B, :C])
is_autopoietic(rn, species)
```

## GF(3) Conservation in CRNs

Map reaction network dynamics to balanced ternary:

```julia
"""
Assign GF(3) trits to reactions for conservation checking.

- Production reactions (∅ → X): PLUS (+1)
- Degradation reactions (X → ∅): MINUS (-1)  
- Conversion reactions (X → Y): ZERO (0)
"""
function reaction_trits(rn::ReactionSystem)
    trits = Dict{Reaction, Int}()
    
    for rx in Catalyst.reactions(rn)
        n_substrates = length(rx.substrates)
        n_products = length(rx.products)
        
        if n_substrates == 0 && n_products > 0
            trits[rx] = 1   # PLUS: production
        elseif n_substrates > 0 && n_products == 0
            trits[rx] = -1  # MINUS: degradation
        else
            trits[rx] = 0   # ZERO: conversion
        end
    end
    
    # Verify conservation
    total = sum(values(trits))
    balanced = total % 3 == 0
    
    return trits, balanced
end
```

## Spatial Reaction-Diffusion

```julia
using Catalyst, MethodOfLines, DomainSets

# Reaction-diffusion PDE
@parameters D_A D_B
@variables x t A(x,t) B(x,t)

# Spatial domain
domain = [x ∈ Interval(0.0, 1.0)]

# Reaction network in each spatial point
rn_spatial = @reaction_network begin
    k1, A + B --> 2B      # Autocatalysis
    k2, B --> A           # Reversion
end

# Add diffusion terms
∂t = Differential(t)
∂x = Differential(x)
∂xx = ∂x ∘ ∂x

eqs = [
    ∂t(A) ~ D_A * ∂xx(A) + reaction_rate(rn_spatial, :A),
    ∂t(B) ~ D_B * ∂xx(B) + reaction_rate(rn_spatial, :B),
]

# Solve with MethodOfLines.jl
```

## ImperativeAffect Events (Issue #1335)

Custom event handling for stochastic CRNs:

```julia
using Catalyst, JumpProcesses

# Define reaction network with events
rn_events = @reaction_network begin
    @parameters k_div k_death threshold
    @species Cells(t) Resources(t)
    
    k_div * Resources, Cells --> 2Cells    # Division uses resources
    k_death, Cells --> ∅                    # Cell death
    1.0, ∅ --> Resources                    # Resource replenishment
end

# Custom affect: cell division only when resources > threshold
function division_affect!(integrator)
    if integrator[:Resources] > integrator.p[:threshold]
        integrator[:Cells] += 1
        integrator[:Resources] -= 1
    end
end

# Attach to jump process
# (Full ImperativeAffect DSL support is WIP per issue #1335)
```

## Links

- [Catalyst.jl](https://github.com/SciML/Catalyst.jl)
- [Documentation](https://docs.sciml.ai/Catalyst/stable/)
- [ModelingToolkit.jl](https://github.com/SciML/ModelingToolkit.jl)
- [Chemical Organization Theory](https://en.wikipedia.org/wiki/Chemical_organization_theory)

## Commands

```bash
just catalyst-demo           # Run Catalyst demonstration
just catalyst-autopoietic    # Autopoietic closure detection
just catalyst-spatial        # Reaction-diffusion example
just catalyst-gf3            # GF(3) conservation check
```

---

*GF(3) Category: ZERO (Coordination/Ergodic) | Chemical computing for multi-agent dynamics*