# CatColab-Causal-Loop Neighbor Skills

**Date**: 2026-01-19
**Trit**: 0 (ERGODIC - coordinator)
**Role**: Systems dynamics feedback analysis

---

## Core Triad

| Skill | Trit | Interface |
|-------|------|-----------|
| **catcolab-regulatory-networks** | -1 | Network structure |
| **catcolab-causal-loop** | 0 | Feedback coordination |
| **catcolab-stock-flow** | +1 | Quantitative dynamics |

**GF(3)**: (-1) + (0) + (+1) = 0 ✓

---

## Immediate Neighbors

### catcolab-regulatory-networks (-1)
**Morphism**: Causal loop ≅ Regulatory (equivalent)
```
Both are signed directed graphs:
  Variable ≅ Node
  Positive link ≅ Activation
  Negative link ≅ Inhibition
```

### catcolab-stock-flow (+1)
**Morphism**: Causal loop → Stock-flow (upgrade)
```
Causal Loop (qualitative)  →  Stock-Flow (quantitative)
  Variable → Stock
  Positive link → Flow with positive coefficient
  Negative link → Flow with negative coefficient

ODEs: Lotka-Volterra semantics
```

### open-games (-1)
**Morphism**: Causal loop → Game theory
```haskell
-- Feedback loops as strategic interactions
causalToGame :: CausalLoop -> OpenGame
causalToGame loop =
  let players = variables loop
      strategies = linkSigns loop
  in composePlayers players strategies
```

### dynamical-system-functor (+1)
**Morphism**: Causal loop → Dynamical system
```julia
# Functor from CausalLoop category to DynSys category
F: CausalLoop → DynSys
F(Variable) = State
F(PositiveLink) = (s, t) → dxₜ/dt ∝ +xₛ
F(NegativeLink) = (s, t) → dxₜ/dt ∝ -xₛ
```

### topos-catcolab (0)
**Morphism**: Loop → CatColab model
```typescript
const cld = catcolab.createModel("causal-loop", "market-dynamics");
cld.addVariable("MarketShare");
cld.addVariable("Revenue");
cld.addPositive("MarketShare", "Revenue");
cld.addNegative("Revenue", "GrowthRate");  // saturation
```

---

## Loop Analysis

### Reinforcing (R) vs Balancing (B)

```
Loop Classification:
  R (Reinforcing): Even # of negative links → exponential
  B (Balancing): Odd # of negative links → equilibrium

Detection Algorithm:
  1. Find all cycles in graph
  2. Count negative links in each cycle
  3. Classify as R (even) or B (odd)
```

---

## Neighbor Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Dynamics | catcolab-regulatory-networks ⊗ catcolab-causal-loop ⊗ catcolab-stock-flow | Structure → Feedback → Quantity |
| Strategy | open-games ⊗ catcolab-causal-loop ⊗ dynamical-system-functor | Game → Loop → System |
| Policy | catcolab-causal-loop ⊗ topos-catcolab ⊗ waddington-landscape | Feedback → Model → Landscape |
