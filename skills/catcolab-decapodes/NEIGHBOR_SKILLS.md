# CatColab-Decapodes Neighbor Skills

**Date**: 2026-01-19
**Trit**: -1 (MINUS - validator/verifier)
**Role**: Discrete Exterior Calculus for PDE modeling

---

## Core Triad

| Skill | Trit | Interface |
|-------|------|-----------|
| **catcolab-decapodes** | -1 | PDE validation |
| **topos-catcolab** | 0 | Platform coordination |
| **catcolab-stock-flow** | +1 | ODE generation |

**GF(3)**: (-1) + (0) + (+1) = 0 ✓

---

## Immediate Neighbors

### catcolab-stock-flow (+1)
**Morphism**: Stock-flow → Decapodes (spatial extension)
```
ODE (lumped)           →  PDE (spatial)
  dT/dt = -κ·ΔT        →  ∂T/∂t = -κ·ΔT + ∇·(D∇T)
  (well-mixed)            (heat equation on mesh)
```

### fokker-planck-analyzer (-1)
**Morphism**: Decapodes ≅ Fokker-Planck
```
Both model distribution evolution:
  Fokker-Planck: ∂P/∂t = -∇·(f·P) + D·∇²P
  Decapodes:     ∂ω/∂t = d(★dω) + advection
                 (via differential forms)
```

### langevin-dynamics (+1)
**Morphism**: Decapodes → Stochastic PDE
```
Deterministic:  ∂T/∂t = κ·ΔT
Stochastic:     dT = κ·ΔT·dt + √(2κ)·dW
                (SPDE via Langevin)
```

### modelica (0)
**Morphism**: Decapodes ≅ Modelica (acausal)
```
Both are equation-based:
  Modelica: der(T) = kappa * laplacian(T)
  Decapodes: ∂T/∂t = κ·★d★d(T)

Key difference: Decapodes uses differential forms
```

### topos-catcolab (0)
**Morphism**: Model → CatColab
```typescript
const heat = catcolab.createModel("decapodes", "heat-transfer");
heat.addForm0("Temperature");
heat.addOperator("gradient", "d0", "Temperature", "TempGrad");
heat.addOperator("laplacian", "Δ", "Temperature", "LapT");
heat.addEquation("∂Temperature/∂t = κ·LapT");
```

---

## De Rham Complex

```
Ω⁰ ──d──► Ω¹ ──d──► Ω² ──d──► Ω³
 │         │         │         │
 ★         ★         ★         ★
 ▼         ▼         ▼         ▼
Ω³ ◄──d── Ω² ◄──d── Ω¹ ◄──d── Ω⁰

Key operators:
  d: exterior derivative (grad, curl, div)
  ★: Hodge star (duality)
  Δ = d★d★ + ★d★d: Laplacian
```

---

## Multiphysics Composition

```julia
# Compose heat + fluid
heat_physics = @decapode begin
  T::Form0
  ∂ₜT == κ*Δ(T)
end

fluid_physics = @decapode begin
  v::Form1
  ∂ₜv == -★(v ∧ ★v) + ν*Δ(v)
end

# Composed: advection-diffusion
combined = compose(heat_physics, fluid_physics,
                   interface=:velocity)
```

---

## Neighbor Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Physics | catcolab-decapodes ⊗ catcolab-stock-flow ⊗ langevin-dynamics | PDE → ODE → SPDE |
| Stochastic | fokker-planck-analyzer ⊗ catcolab-decapodes ⊗ langevin-dynamics | Distribution → Forms → Noise |
| Simulation | modelica ⊗ catcolab-decapodes ⊗ topos-catcolab | Acausal → DEC → Platform |
