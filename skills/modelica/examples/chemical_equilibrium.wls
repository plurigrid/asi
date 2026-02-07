#!/usr/bin/env wolframscript
(* Chemical Equilibrium via Modelica *)
(* Demonstrates chemputation-native acausal modeling *)

Print["═══════════════════════════════════════════════════════════════"]
Print["  Modelica Skill Demo: Chemical Reaction Equilibrium"]
Print["═══════════════════════════════════════════════════════════════\n"]

(* Create a simple A + B ⇌ C reaction model *)
Print["Creating reaction model: A + B ⇌ C\n"]

reactionModel = CreateSystemModel["ChemDemo.AB_C", {
    (* Rate equations from mass action kinetics *)
    A'[t] == -kf * A[t] * B[t] + kr * C[t],
    B'[t] == -kf * A[t] * B[t] + kr * C[t],
    C'[t] == +kf * A[t] * B[t] - kr * C[t]
}, t, <|
    "ParameterValues" -> {
        kf -> 0.1,   (* Forward rate constant *)
        kr -> 0.01   (* Reverse rate constant *)
    },
    "InitialValues" -> {
        A -> 1.0,    (* Initial [A] *)
        B -> 1.0,    (* Initial [B] *)
        C -> 0.0     (* Initial [C] *)
    },
    "SimulationSettings" -> {
        "StopTime" -> 100
    }
|>]

Print["Model created: ", reactionModel["ModelName"]]
Print["Equations: ", reactionModel["SystemEquations"]]

(* Simulate *)
Print["\nSimulating to t=100..."]
sim = SystemModelSimulate[reactionModel, 100];

(* Find equilibrium *)
Print["\nFinding equilibrium..."]
eq = FindSystemModelEquilibrium[reactionModel];

Print["\nEquilibrium concentrations:"]
Print["  [A]_eq = ", eq[[1, 1, 2]]]
Print["  [B]_eq = ", eq[[1, 2, 2]]]
Print["  [C]_eq = ", eq[[1, 3, 2]]]

(* Verify conservation *)
total0 = 1.0 + 1.0 + 0.0;  (* Initial total *)
totalEq = eq[[1, 1, 2]] + eq[[1, 2, 2]] + eq[[1, 3, 2]];
Print["\nMass conservation check:"]
Print["  Initial total: ", total0]
Print["  Equilibrium total: ", totalEq]
Print["  Conserved: ", Abs[total0 - totalEq] < 0.001]

(* Keq check *)
Keq = eq[[1, 3, 2]] / (eq[[1, 1, 2]] * eq[[1, 2, 2]]);
Print["\nEquilibrium constant K_eq = ", Keq]
Print["Expected (kf/kr = 0.1/0.01) = 10"]
Print["Match: ", Abs[Keq - 10] < 0.1]

(* Export trajectory plot *)
Print["\nExporting trajectory plot..."]
Export["equilibrium_trajectory.png", 
    SystemModelPlot[sim, {A, B, C}, 
        PlotLabel -> "A + B ⇌ C Reaction Kinetics",
        PlotLegends -> {"[A]", "[B]", "[C]"}]
]
Print["Saved: equilibrium_trajectory.png"]

Print["\n═══════════════════════════════════════════════════════════════"]
Print["  GF(3) Triad: modelica (0) simulation complete"]
Print["═══════════════════════════════════════════════════════════════"]
