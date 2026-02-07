---
name: catcolab-stock-flow
description: CatColab Stock-and-Flow Diagrams - epidemiological and ecological modeling with stocks (accumulations), flows (rates), and mass-action ODE semantics for SIR models and population dynamics.
version: 1.0.0
---

# CatColab Stock-and-Flow Diagrams: Epidemiology & Ecology

**Trit**: +1 (PLUS - generator)
**Color**: Orange (#FF8C00)

## Overview

Stock-and-Flow diagrams in CatColab model systems with:
- **Stocks**: Accumulations (populations, inventories, quantities)
- **Flows**: Rates of change between stocks
- **Links**: Auxiliary connections influencing flow rates
- **Mass-action semantics**: Automatic ODE generation

This is the foundation for epidemiological models (SIR), ecological models (Lotka-Volterra), and resource dynamics.

## Mathematical Foundation

```
┌─────────────────────────────────────────────────────┐
│           STOCK-AND-FLOW DIAGRAM                     │
├─────────────────────────────────────────────────────┤
│  Stocks (Accumulations):                             │
│    [S] Susceptible  [I] Infected  [R] Recovered      │
│                                                      │
│  Flows (Rates):                                      │
│    infection: S → I                                  │
│    recovery: I → R                                   │
│                                                      │
│  Links (Influences):                                 │
│    I ──link──► infection (infected influence rate)   │
│                                                      │
│  Diagram:                                            │
│    ┌───┐  infection  ┌───┐  recovery  ┌───┐         │
│    │ S │ ═══════════► │ I │ ═══════════► │ R │         │
│    └───┘             └───┘             └───┘         │
│      ▲                 │                             │
│      └────── link ─────┘                             │
└─────────────────────────────────────────────────────┘
```

## Double Theory

```rust
// Stock-Flow double theory
pub fn th_stock_flow() -> DiscreteDblTheory {
    let mut cat = FpCategory::new();

    // Object type
    cat.add_ob_generator(name("Stock"));

    // Morphism types
    cat.add_mor_generator(name("Flow"), name("Stock"), name("Stock"));
    cat.add_mor_generator(name("Link"), name("Stock"), name("Stock"));

    cat.into()
}
```

## Mass-Action ODE Semantics

CatColab generates **mass-action ODEs** from stock-flow diagrams:

```
For flow f: A → B influenced by links from stocks {Sᵢ}:

  rate(f) = k_f · A · ∏ᵢ Sᵢ

  dA/dt = -rate(f) + (inflows to A)
  dB/dt = +rate(f) + (other flows)
```

### SIR Model ODEs

```
Stocks: S, I, R
Flows: infection (S→I), recovery (I→R)
Links: I influences infection

Generated ODEs:
  dS/dt = -β·S·I
  dI/dt = +β·S·I - γ·I
  dR/dt = +γ·I

Where β = infection rate, γ = recovery rate
```

## CatColab Implementation

### Stock Declaration

```typescript
{
  "type": "ObDecl",
  "name": "Susceptible",
  "theory_type": "Stock",
  "description": "population not yet infected"
}
```

### Flow Declaration

```typescript
{
  "type": "MorDecl",
  "name": "infection",
  "dom": "Susceptible",
  "cod": "Infected",
  "theory_type": "Flow",
  "description": "rate at which susceptibles become infected"
}
```

### Link Declaration

```typescript
{
  "type": "MorDecl",
  "name": "contact_influence",
  "dom": "Infected",
  "cod": "Susceptible",
  "theory_type": "Link",
  "description": "infected population influences infection rate"
}
```

## Practical Examples

### Example 1: SIR Epidemic Model

```
Stocks: S (Susceptible), I (Infected), R (Recovered)

Flows:
  infection: S → I
  recovery: I → R

Links:
  I → infection (more infected = faster spread)

Parameters:
  β (infection rate): 0.3
  γ (recovery rate): 0.1

R₀ = β/γ = 3.0 (epidemic threshold > 1)
```

### Example 2: SEIR with Exposed

```
Stocks: S, E (Exposed), I, R

Flows:
  exposure: S → E
  onset: E → I
  recovery: I → R

Links:
  I → exposure (infected spread disease)

Addition: Latency period before becoming infectious
```

### Example 3: Predator-Prey (Lotka-Volterra)

```
Stocks: Rabbits, Foxes

Flows:
  rabbit_birth: ∅ → Rabbits
  rabbit_death: Rabbits → ∅
  predation: Rabbits → Foxes
  fox_death: Foxes → ∅

Links:
  Rabbits → rabbit_birth (reproduction)
  Foxes → predation (hunting)
  Foxes → rabbit_death (hunting pressure)

ODEs:
  dR/dt = αR - βRF
  dF/dt = δRF - γF
```

### Example 4: Resource Depletion

```
Stocks: Resource, Capital, Population

Flows:
  extraction: Resource → Capital
  investment: Capital → Capital
  consumption: Capital → ∅
  birth: ∅ → Population
  death: Population → ∅

Links:
  Population → extraction
  Capital → birth
  Resource → extraction (scarcity effect)
```

## Analysis Capabilities

CatColab provides for stock-flow models:

- **ODE Integration**: Numerical simulation
- **Steady State**: Fixed point analysis
- **Sensitivity**: Parameter sweeps
- **Composition**: Combine models via shared stocks

## Stratification & Composition

Stock-flow diagrams compose via **stratification**:

```julia
# Base SIR model
sir = @acset StockFlow begin
  Stock = [:S, :I, :R]
  Flow = [(:S, :I), (:I, :R)]
end

# Age-stratified version (young/old)
age_strata = @acset Strata begin
  Stratum = [:Young, :Old]
end

# Compose: SIR × Age = 6 stocks (S_young, S_old, ...)
stratified_sir = stratify(sir, age_strata)
```

## GF(3) Triads

```
catcolab-regulatory-networks (-1) ⊗ catcolab-causal-loop (0) ⊗ catcolab-stock-flow (+1) = 0 ✓
catcolab-ologs (-1) ⊗ topos-catcolab (0) ⊗ catcolab-stock-flow (+1) = 0 ✓
```

## Commands

```bash
# Create stock-flow model
just catcolab-new primitive-stock-flow "sir-model"

# Generate mass-action ODEs
just catcolab-analyze sir-model --odes

# Simulate epidemic
just catcolab-simulate sir-model --params "β=0.3,γ=0.1" --time 100

# Stratify by age
just catcolab-stratify sir-model age-strata

# Export to AlgebraicJulia
just catcolab-export sir-model --format=julia
```

## Integration with AlgebraicJulia

```julia
using AlgebraicPetri
using Catlab

# Load CatColab model
model = load_stockflow("sir-model.json")

# Convert to Petri net
petri = stockflow_to_petri(model)

# Simulate with DifferentialEquations.jl
using OrdinaryDiffEq
u0 = [990.0, 10.0, 0.0]  # S, I, R
prob = ODEProblem(vectorfield(petri), u0, (0.0, 100.0))
sol = solve(prob, Tsit5())
```

## References

- Baez & Pollard (2017) "A Compositional Framework for Reaction Networks"
- Libkind et al. (2022) "An algebraic framework for structured epidemic modeling"
- [CatColab Stock-Flow Help](https://catcolab.org/help/logics/primitive-stock-flow)
- [AlgebraicPetri.jl](https://algebraicjulia.github.io/AlgebraicPetri.jl/)

---

**Skill Name**: catcolab-stock-flow
**Type**: Epidemiology / Population Dynamics
**Trit**: +1 (PLUS)
**GF(3)**: Conserved via triadic composition
