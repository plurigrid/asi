# Wolfram Language Modelica API Reference

## Core Functions

### SystemModel
```mathematica
SystemModel["model"]                    (* Get model representation *)
SystemModel["model"]["property"]        (* Query property *)
SystemModel["model", <|changes...|>]    (* Modify and return new model *)
```

### SystemModelSimulate
```mathematica
SystemModelSimulate[model]                                    (* Default settings *)
SystemModelSimulate[model, tmax]                              (* 0 to tmax *)
SystemModelSimulate[model, {tmin, tmax}]                      (* Time interval *)
SystemModelSimulate[model, vars, {tmin, tmax}]                (* Store only vars *)
SystemModelSimulate[model, <|
  "ParameterValues" -> {p -> val, ...},
  "InitialValues" -> {x -> x0, ...},
  "InputFunctions" -> {"u" -> func, ...}
|>]
```

**Supported model types**:
- `SystemModel[...]` — Modelica models
- `StateSpaceModel[...]` — State-space
- `TransferFunctionModel[...]` — Transfer function
- `AffineStateSpaceModel[...]` — Affine
- `NonlinearStateSpaceModel[...]` — Nonlinear

### CreateSystemModel
```mathematica
CreateSystemModel[sys]                          (* From state-space/transfer function *)
CreateSystemModel[eqns, t]                      (* From differential equations *)
CreateSystemModel["Name", eqns, t, types]       (* Named, with type specs *)
CreateSystemModel["Name", eqns, t, <|
  "ParameterValues" -> {...},
  "InitialValues" -> {...},
  "ExtendsModels" -> {"Partial.Model"},
  "SimulationSettings" -> {"StopTime" -> 10}
|>]
```

### ConnectSystemModelComponents
```mathematica
ConnectSystemModelComponents[
  {"c1" ∈ comp1, "c2" ∈ comp2, ...},
  {"c1.port1" -> "c2.port2", ...}
]
ConnectSystemModelComponents["NewModel", components, connections, <|
  "ParameterValues" -> {...},
  "InitialValues" -> {...}
|>]
```

### SystemModelLinearize
```mathematica
SystemModelLinearize[model]                     (* At equilibrium *)
SystemModelLinearize[model, "InitialValues"]    (* At initial values *)
SystemModelLinearize[model, "EquilibriumValues"]
SystemModelLinearize[model, sim, "FinalValues"] (* From simulation *)
SystemModelLinearize[model, constraints]        (* With constraints *)
```

### FindSystemModelEquilibrium
```mathematica
FindSystemModelEquilibrium[model]
FindSystemModelEquilibrium[model, {x -> val, ...}]  (* Constrained *)
FindSystemModelEquilibrium[model, {{{x, x0}}, {{u, u0}}, {{y, y0}}}]  (* Start point *)
```

## Solver Methods

| Method | Description |
|--------|-------------|
| `"DASSL"` | DASSL DAE solver (default) |
| `"CVODES"` | CVODES ODE solver |
| `"Radau5"` | Implicit Runge-Kutta |
| `"Dopri5"` | Explicit Runge-Kutta |
| `"ExplicitEuler"` | Fixed-step explicit Euler |
| `"ExplicitMidpoint"` | Fixed-step midpoint |
| `"ImplicitEuler"` | Fixed-step implicit Euler |
| `"NDSolve"` | Use Wolfram's NDSolve |

### Solver Options
```mathematica
Method -> {"DASSL",
  "InterpolationPoints" -> 500,
  "MaxStepSize" -> 0.01,
  "MinStepSize" -> 1*^-10,
  "RelativeTolerance" -> 1*^-6,
  "AbsoluteTolerance" -> 1*^-8
}
```

## Import/Export Formats

| Format | Import | Export | Description |
|--------|--------|--------|-------------|
| `"MO"` | ✓ | ✓ | Modelica source (.mo) |
| `"SME"` | ✓ | — | Simulation results |
| `"FMU"` | ✓ | ✓ | Functional Mock-up Unit |
| `"SMA"` | ✓ | ✓ | System Modeler Archive |

## SystemModel Properties

### Model Information
- `"Description"` — Description string
- `"ModelName"` — Fully qualified name
- `"Diagram"` — Graphical diagram (Graphics)
- `"ModelicaIcon"` — Icon view
- `"ModelicaString"` — Modelica source code
- `"SourceFile"` — File path
- `"Domain"` — Domain usage association
- `"SimulationSettings"` — Default options

### Equations and Variables
- `"SystemEquations"` — ODE/DAE equations
- `"InitialEquations"` — Initial conditions
- `"SystemVariables"` — State variables
- `"InputVariables"` — Inputs
- `"OutputVariables"` — Outputs
- `"DiscreteVariables"` — Event-based variables
- `"ParameterNames"` — All parameters

### Values
- `"InitialValues"` — Default initial values
- `"ParameterValues"` — Default parameter values

### Structure
- `"Components"` — Hierarchical components
- `"Connections"` — Component connections
- `"Connectors"` — Interface connectors
- `"ExtendsModels"` — Inherited models

## Legacy WSMLink API

```mathematica
Needs["WSMLink`"]

(* Simulation *)
WSMSimulate["model", tmax, WSMParameterValues -> {...}]
WSMRealTimeSimulate["model"]

(* Analysis *)
WSMLinearize["model"]
WSMFindEquilibrium["model"]
WSMModelData["model", "property"]

(* Creation *)
WSMCreateModel["name", eqns, t]
WSMConnectComponents[...]
```

## References

- https://reference.wolfram.com/language/ref/SystemModel.html
- https://reference.wolfram.com/language/ref/SystemModelSimulate.html
- https://reference.wolfram.com/language/ref/CreateSystemModel.html
- https://reference.wolfram.com/language/ref/ConnectSystemModelComponents.html
- https://reference.wolfram.com/language/ref/SystemModelLinearize.html
- https://reference.wolfram.com/language/ref/FindSystemModelEquilibrium.html
