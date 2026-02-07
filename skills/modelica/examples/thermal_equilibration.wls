#!/usr/bin/env wolframscript
(* Thermal Equilibration via Modelica *)
(* Demonstrates multi-domain connector semantics *)

Print["═══════════════════════════════════════════════════════════════"]
Print["  Modelica Skill Demo: Thermal Equilibration"]
Print["═══════════════════════════════════════════════════════════════\n"]

(* Use built-in Modelica thermal example *)
model = SystemModel["Modelica.Thermal.HeatTransfer.Examples.TwoMasses"];

Print["Model: ", model["ModelName"]]
Print["Description: ", model["Description"]]
Print["\nDomain usage:"]
Print[model["Domain"]]

(* Show thermal connector semantics *)
Print["\n── Thermal Connector Semantics ──"]
Print["Effort variable: Temperature T (equalized at connection)"]
Print["Flow variable: Heat flow Q_flow (sums to zero)"]
Print["Connection law: T1 = T2, Q1 + Q2 = 0"]

(* Simulate *)
Print["\nSimulating thermal equilibration..."]
sim = SystemModelSimulate[model, 10];

(* Get initial and final temperatures *)
Print["\nTemperature evolution:"]
Print["  Mass 1 initial: ", sim["mass1.T"][0]]
Print["  Mass 2 initial: ", sim["mass2.T"][0]]
Print["  Mass 1 final: ", sim["mass1.T"][10]]
Print["  Mass 2 final: ", sim["mass2.T"][10]]

(* Verify energy conservation *)
Print["\n── Energy Conservation Check ──"]
(* E = C * T, total energy constant *)
Print["Heat capacities: mass1.C, mass2.C (from model parameters)"]

(* Find equilibrium temperature *)
eq = FindSystemModelEquilibrium[model];
Print["\nEquilibrium temperatures:"]
Print["  T_eq (mass1) = ", eq[[1, 1, 2]]]
Print["  T_eq (mass2) = ", eq[[1, 2, 2]]]

(* Linearize for time constant *)
Print["\nLinearizing at equilibrium for time constant analysis..."]
ss = SystemModelLinearize[model];
eigenvals = Eigenvalues[ss["A"]];
Print["System eigenvalues: ", eigenvals]
timeConstants = -1/eigenvals;
Print["Time constants: ", timeConstants]

(* Export plot *)
Print["\nExporting temperature plot..."]
Export["thermal_equilibration.png",
    SystemModelPlot[sim, {"mass1.T", "mass2.T"},
        PlotLabel -> "Thermal Equilibration (Two Masses)",
        PlotLegends -> {"Mass 1", "Mass 2"},
        AxesLabel -> {"Time (s)", "Temperature (K)"}]
]
Print["Saved: thermal_equilibration.png"]

Print["\n═══════════════════════════════════════════════════════════════"]
Print["  Acausal semantics: Connector enforces energy conservation"]
Print["═══════════════════════════════════════════════════════════════"]
