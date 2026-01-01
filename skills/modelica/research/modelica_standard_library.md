# Modelica Standard Library 4.0.0

## Package Structure

| Package | Description | Components |
|---------|-------------|------------|
| `Modelica.Blocks` | Input/output control blocks | ~200 |
| `Modelica.ComplexBlocks` | Complex signal blocks | ~50 |
| `Modelica.Clocked` | Synchronous control | ~30 |
| `Modelica.StateGraph` | State machines | ~30 |
| `Modelica.Electrical` | Electrical systems | ~200 |
| `Modelica.Magnetic` | Magnetic circuits | ~40 |
| `Modelica.Mechanics` | Mechanical systems | ~150 |
| `Modelica.Fluid` | Thermo-fluid flow | ~100 |
| `Modelica.Media` | Media properties | ~100 |
| `Modelica.Thermal` | Heat transfer | ~50 |
| `Modelica.Math` | Mathematical functions | ~80 |
| `Modelica.ComplexMath` | Complex math | ~40 |
| `Modelica.Utilities` | Scripting utilities | ~50 |
| `Modelica.Constants` | Physical constants | ~20 |
| `Modelica.Units` | SI units | ~100 |

**Total**: 1417 component models, 512 examples, 1219 functions

## Domain Connectors

### Electrical (`Modelica.Electrical.Analog.Interfaces`)
```modelica
connector Pin
  SI.Voltage v;      // Effort (equalized)
  flow SI.Current i; // Flow (summed to 0)
end Pin;
```

### Translational (`Modelica.Mechanics.Translational.Interfaces`)
```modelica
connector Flange
  SI.Position s;     // Effort
  flow SI.Force f;   // Flow
end Flange;
```

### Rotational (`Modelica.Mechanics.Rotational.Interfaces`)
```modelica
connector Flange
  SI.Angle phi;       // Effort
  flow SI.Torque tau; // Flow
end Flange;
```

### Thermal (`Modelica.Thermal.HeatTransfer.Interfaces`)
```modelica
connector HeatPort
  SI.Temperature T;       // Effort
  flow SI.HeatFlowRate Q_flow; // Flow
end HeatPort;
```

### Fluid (`Modelica.Fluid.Interfaces`)
```modelica
connector FluidPort
  SI.AbsolutePressure p;      // Effort
  flow SI.MassFlowRate m_flow; // Flow
  stream SI.SpecificEnthalpy h_outflow;
end FluidPort;
```

## Key Examples

### Electrical
- `Modelica.Electrical.Analog.Examples.ChuaCircuit` — Chaotic circuit
- `Modelica.Electrical.Analog.Examples.RCCircuit` — RC filter
- `Modelica.Electrical.Analog.Examples.HeatingResistor` — Coupled

### Mechanical
- `Modelica.Mechanics.Rotational.Examples.CoupledClutches` — Drive train
- `Modelica.Mechanics.MultiBody.Examples.Simple.DoublePendulum` — 3D dynamics
- `Modelica.Mechanics.Translational.Examples.Brake` — Friction

### Thermal/Fluid
- `Modelica.Thermal.HeatTransfer.Examples.TwoMasses` — Heat exchange
- `Modelica.Fluid.Examples.Tanks.ThreeTanks` — Tank dynamics
- `Modelica.Fluid.Examples.HeatingSystem` — HVAC

### Control
- `Modelica.Blocks.Examples.PID_Controller` — PID control
- `Modelica.StateGraph.Examples.ControlledTanks` — Discrete+continuous

## Modelica Language Basics

### Model Structure
```modelica
model MyModel
  // Imports
  import SI = Modelica.Units.SI;
  
  // Parameters (time-invariant)
  parameter SI.Resistance R = 1;
  
  // Variables
  SI.Voltage v;
  SI.Current i;
  
  // Connectors
  Modelica.Electrical.Analog.Interfaces.Pin p, n;
  
equation
  // Constitutive equation
  v = R * i;
  
  // Port equations
  v = p.v - n.v;
  i = p.i;
  n.i = -i;
end MyModel;
```

### Connection Semantics
```modelica
connect(a.p, b.n);
// Generates:
// a.p.v = b.n.v;           (effort equalized)
// a.p.i + b.n.i = 0;       (flow summed)
```

### Hybrid Events
```modelica
when x > threshold then
  y = pre(y) + 1;
end when;
```

## Physical Units (Modelica.Units.SI)

| Unit | Type | Description |
|------|------|-------------|
| `SI.Voltage` | Real | Electric potential (V) |
| `SI.Current` | Real | Electric current (A) |
| `SI.Resistance` | Real | Resistance (Ω) |
| `SI.Temperature` | Real | Thermodynamic temp (K) |
| `SI.Pressure` | Real | Pressure (Pa) |
| `SI.Force` | Real | Force (N) |
| `SI.Torque` | Real | Torque (N·m) |
| `SI.MassFlowRate` | Real | Mass flow (kg/s) |

## Modelica Specification Version

**Current**: Modelica Language Specification 3.6

Key features:
- Synchronous language elements
- State machines
- Stream connectors (for fluid)
- Spatially distributed models
- Operator overloading

## References

- https://specification.modelica.org
- https://doc.modelica.org/Modelica%204.0.0/
- https://github.com/modelica/ModelicaStandardLibrary
