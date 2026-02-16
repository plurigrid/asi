# CatColab-Stock-Flow Neighbor Skills

**Date**: 2026-01-19
**Trit**: +1 (PLUS - generator)
**Role**: Epidemiological and ecological population modeling

---

## Core Triad

| Skill | Trit | Interface |
|-------|------|-----------|
| **catcolab-regulatory-networks** | -1 | Network structure |
| **catcolab-causal-loop** | 0 | Feedback coordination |
| **catcolab-stock-flow** | +1 | Population generation |

**GF(3)**: (-1) + (0) + (+1) = 0 ✓

---

## Immediate Neighbors

### catcolab-causal-loop (0)
**Morphism**: Causal → Stock-flow (quantitative upgrade)
```
Causal Loop (qualitative)  →  Stock-Flow (quantitative)
  Variable A ──(+)──► B   →   Stock A ═══flow═══► Stock B
                               with rate ∝ A·B (mass action)
```

### catcolab-decapodes (-1)
**Morphism**: Stock-flow → PDE (spatial)
```
ODE (stock-flow)  →  PDE (decapodes)
  dS/dt = f(S,I)  →  ∂S/∂t = f(S,I) + D·∇²S
                      (add spatial diffusion)
```

### alife (+1)
**Morphism**: Stock-flow → Artificial life
```python
# Stock-flow as agent population dynamics
def population_step(stocks, flows, params):
    for flow in flows:
        rate = mass_action(stocks, flow, params)
        stocks[flow.source] -= rate
        stocks[flow.target] += rate
```

### crn-topology (-1)
**Morphism**: Stock-flow ≅ Petri net
```
Stock-Flow diagram ≅ Petri net
  Stock → Place (holds tokens)
  Flow → Transition (moves tokens)
  Link → Arc (influences rate)
```

### topos-catcolab (0)
**Morphism**: Model → CatColab
```typescript
const sir = catcolab.createModel("primitive-stock-flow", "SIR");
sir.addStock("Susceptible");
sir.addStock("Infected");
sir.addStock("Recovered");
sir.addFlow("infection", "Susceptible", "Infected");
sir.addFlow("recovery", "Infected", "Recovered");
sir.addLink("Infected", "infection");  // I influences rate
```

### fokker-planck-analyzer (-1)
**Morphism**: Stock-flow → Stochastic dynamics
```
Deterministic:  dS/dt = -βSI
Stochastic:     dS = -βSI·dt + σ√(βSI)·dW
                (chemical master equation)
```

---

## Mass-Action Semantics

```julia
# CatColab generates mass-action ODEs
# For flow f: A → B with links from {Sᵢ}:
#   rate(f) = k_f · A · ∏ᵢ Sᵢ

# SIR Example:
#   dS/dt = -β·S·I
#   dI/dt = +β·S·I - γ·I
#   dR/dt = +γ·I
```

---

## Stratification & Composition

```julia
# Stratify SIR by age
base_sir = @acset StockFlow begin
  Stock = [:S, :I, :R]
  Flow = [(:S, :I), (:I, :R)]
end

age_strata = @acset Strata begin
  Stratum = [:Young, :Old]
end

# Result: 6 stocks (S_young, S_old, I_young, ...)
stratified = stratify(base_sir, age_strata)
```

---

## ACSet Infrastructure Bridges

### structured-decomp (0)
**Morphism**: Stock-flow → Sheaf on tree decomposition
```julia
# Decompose large epidemiological model
decomp = tree_decomposition(sir_network)
# Solve locally, glue via sheaf condition
local_sols = [solve_ode(bag) for bag in bags(decomp)]
global_sol = glue_solutions(local_sols, adhesions(decomp))
```

### acsets-hatchery (0)
**Morphism**: Stock-flow schema → ACSet instance
```julia
@acset StockFlowModel(SchStockFlow) begin
  Stock = [:S, :I, :R]
  Flow = 2; flow_src = [1, 2]; flow_tgt = [2, 3]
  Link = 1; link_src = [2]; link_tgt = [1]  # I influences S→I
end
```

### algebraic-rewriting (-1)
**Morphism**: Model composition via colimit
```julia
# Compose SIR with Vaccination
composed = @acset_colim StockFlow begin
  sir::SIR; vax::Vax
  # Identify S in both
  apex(sir.S, vax.S_unvax)
end
```

---

## Neighbor Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Epidemiology | catcolab-causal-loop ⊗ catcolab-stock-flow ⊗ alife | Feedback → Population → Life |
| Spatial | catcolab-stock-flow ⊗ catcolab-decapodes ⊗ fokker-planck-analyzer | ODE → PDE → Stochastic |
| Chemistry | crn-topology ⊗ catcolab-stock-flow ⊗ assembly-index | CRN → Dynamics → Complexity |
| **Cross-layer** | structured-decomp (0) ⊗ catcolab-stock-flow (+1) ⊗ tasks-acset (-1) | Decomp → ODE → Tasks |
| **Deep** | acsets-hatchery (0) ⊗ catcolab-stock-flow (+1) ⊗ catcolab-ologs (-1) | Instance → Dynamics → Ontology |
