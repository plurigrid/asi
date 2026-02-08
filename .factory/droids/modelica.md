---
name: modelica
description: "Modelica acausal equation-based multi-domain modeling via Wolfram Language. Chemputation-native simulation with automatic conservation laws. Lambda-Modelica bridge for string diagram semantics. Fixed point classification for 3-coloring/3-MATCH systems."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Modelica Skill: Acausal Multi-Domain Modeling

**Status**: ✅ Production Ready + Triplet #2 + Lambda Bridge + Fixed Point Classification
**Trit**: 0 (ERGODIC - coordinator)
**Color**: #26D826 (Green)
**Principle**: Constraints over causality + Stochastic Equilibrium Verification + String Diagram Semantics
**Frame**: $0 = F(x, y, t)$ constraint satisfaction + Fokker-Planck convergence + Lambda↔Modelica bridge

---

## Overview

**Modelica** is the **chemputation-native** modeling language. Unlike imperative programming ($y = f(x)$), Modelica defines **constraints** that the solver satisfies—directly analogous to thermodynamic settling and reaction-diffusion equilibria.

1. **Acausal Semantics**: Equations, not assignments
2. **Conservation Laws**: Automatic Kirchhoff at connectors
3. **Multi-Domain**: Electrical, mechanical, fluid, thermal unified
4. **DAE Solving**: Differential-algebraic equations with index reduction

## Core Framework

### Wolfram Language API (Modern v11.3+)

```mathematica
(* Import and explore *)
model = SystemModel["Modelica.Electrical.Analog.Examples.ChuaCircuit"];
model["Description"]
model["Diagram"]
model["SystemEquations"]

(* Simulate *)
sim = SystemModelSimulate[model, 100];
SystemModelPlot[sim, {"C1.v", "C2.v"}]

(* Create from equations *)
CreateSystemModel["MyModel", {
  x''[t] + 2*zeta*omega*x'[t] + omega^2*x[t] == F[t]
}, t, <|
  "ParameterValues" -> {omega -> 1, zeta -> 0.1},
  "InitialValues" -> {x -> 0, x' -> 0}
|>]

(* Connect components *)
ConnectSystemModelComponents[
  {"R" ∈ "Modelica.Electrical.Analog.Basic.Resistor",
   "C" ∈ "Modelica.Electrical.Analog.Basic.Capacitor",
   "V" ∈ "Modelica.Electrical.Analog.Sources.SineVoltage"},
  {"V.p" -> "R.p", "R.n" -> "C.p", "C.n" -> "V.n"}
]

(* Linearize for control design *)
eq = FindSystemModelEquilibrium[model];
ss = SystemModelLinearize[model, eq];  (* Returns StateSpaceModel *)
```

## Key Concepts

### 1. Acausal vs Causal (Chemputation Alignment)

| Paradigm | Semantics |