# Chemputation Integration: Modelica ↔ XDL ↔ CRN

## GF(3) Chemputation Triad

```
turing-chemputer (-1) ⊗ modelica (0) ⊗ crn-topology (+1) = 0 ✓
```

| Skill | Trit | Role | Domain |
|-------|------|------|--------|
| turing-chemputer | -1 | MINUS (Executor) | XDL → Hardware |
| modelica | 0 | ERGODIC (Coordinator) | Thermodynamic simulation |
| crn-topology | +1 | PLUS (Generator) | Reaction network topology |

## Integration Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Chemputation Pipeline                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐          │
│  │ crn-topology│    │  modelica   │    │   turing-   │          │
│  │    (+1)     │───▶│     (0)     │───▶│  chemputer  │          │
│  │   GENERATE  │    │  SIMULATE   │    │   (-1)      │          │
│  └─────────────┘    └─────────────┘    │  EXECUTE    │          │
│        │                   │           └─────────────┘          │
│        │                   │                  │                  │
│   ReactionGraph      SystemModel           XDL Program          │
│   (ACSets.jl)       (Wolfram Lang)        (XML/Python)          │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## Data Flow

### 1. CRN → Modelica

```julia
# crn-topology generates reaction graph (ACSets.jl)
using Catlab, AlgebraicPetri

rxn_network = @acset LabelledReactionNet begin
    S = [:A, :B, :C]
    T = [:forward, :reverse]
    I = [1, 2]  # A + B → ...
    O = [3]     # ... → C
    is = [1, 1]
    it = [1, 2]
    os = [3]
    ot = [1]
end

# Export to Modelica-compatible ODE format
function crn_to_modelica_eqns(net::LabelledReactionNet)
    species = net[:, :sname]
    rates = generate_rate_equations(net)
    
    """
    model $(join(species, "_"))_Reaction
        Real $(join(species, ", "));
        parameter Real kf = 0.1, kr = 0.01;
    equation
        $(join(rates, "\n        "))
    end $(join(species, "_"))_Reaction;
    """
end
```

### 2. Modelica Simulation

```mathematica
(* Import CRN-generated model *)
Import["reaction.mo", "MO"]

(* Or create directly *)
CreateSystemModel["Chem.ABC_Reaction", {
    (* From CRN topology *)
    A'[t] == -kf * A[t] * B[t] + kr * C[t],
    B'[t] == -kf * A[t] * B[t] + kr * C[t],
    C'[t] == +kf * A[t] * B[t] - kr * C[t],
    (* Conservation law (automatic from CRN structure) *)
    A[t] + B[t] + C[t] == total
}, t, <|
    "ParameterValues" -> {kf -> 0.1, kr -> 0.01, total -> 2},
    "InitialValues" -> {A -> 1, B -> 1, C -> 0}
|>]

(* Simulate to find equilibrium conditions *)
sim = SystemModelSimulate["Chem.ABC_Reaction", 100];
eq = FindSystemModelEquilibrium["Chem.ABC_Reaction"];

(* Extract equilibrium concentrations for XDL *)
equilibrium_concs = {
    "A" -> eq[[1, 1, 2]],
    "B" -> eq[[1, 2, 2]],
    "C" -> eq[[1, 3, 2]]
}
```

### 3. Modelica → XDL

```python
# modelica simulation results → XDL synthesis protocol
from turing_chemputer import XDLProgram

def modelica_to_xdl(equilibrium_concs, reaction_params):
    """Generate XDL from Modelica equilibrium analysis."""
    xdl = XDLProgram()
    
    # Hardware setup from reaction requirements
    xdl.add_hardware("reactor1", volume="100 mL", type="jacketed")
    xdl.add_hardware("heater1", type="heater")
    
    # Reagent addition based on stoichiometry
    for species, target_conc in equilibrium_concs.items():
        amount = target_conc * 100  # Scale to 100mL
        xdl.add(reagent=species, vessel="reactor1", amount=f"{amount} mmol")
    
    # Temperature from Modelica thermal analysis
    optimal_temp = reaction_params.get("T_opt", "25 °C")
    reaction_time = reaction_params.get("t_eq", "2 h")
    
    xdl.heat("reactor1", temp=optimal_temp, time=reaction_time)
    
    return xdl.to_xml()
```

## Thermal Integration

Modelica excels at multi-domain thermal analysis:

```mathematica
(* Reaction with heat effects *)
ConnectSystemModelComponents[
    (* Chemical reactor *)
    {"reactor" ∈ CreateSystemModel[{
        A'[t] == -k[t] * A[t],
        (* Arrhenius temperature dependence *)
        k[t] == A_factor * Exp[-Ea / (R * T[t])]
    }, t]},
    
    (* Thermal jacket *)
    {"jacket" ∈ "Modelica.Thermal.HeatTransfer.Components.HeatCapacitor",
     "heater" ∈ "Modelica.Thermal.HeatTransfer.Sources.FixedHeatFlow"},
    
    (* Connect thermal port *)
    {"reactor.heatPort" -> "jacket.port",
     "heater.port" -> "jacket.port"},
     
    <|"ParameterValues" -> {
        "jacket.C" -> 1000,  (* Heat capacity J/K *)
        "heater.Q_flow" -> 100  (* Heat input W *)
    }|>
]
```

## Narya Verification Bridge

Simulation trajectories become verifiable event logs:

```python
from narya_proofs import NaryaProofRunner, Event

def modelica_sim_to_narya(sim_data, context="chem-reaction"):
    """Convert Modelica simulation to Narya-verifiable events."""
    events = []
    
    for i, (t, state) in enumerate(sim_data):
        # Assign trit based on reaction progress
        if i == 0:
            trit = -1  # Initial (BACKFILL)
        elif i == len(sim_data) - 1:
            trit = +1  # Equilibrium reached (LIVE)
        else:
            trit = 0   # Processing (VERIFY)
        
        events.append(Event(
            event_id=f"sim_{i}",
            context=context,
            trit=trit,
            timestamp=t,
            content={"state": state, "time": t}
        ))
    
    return events

# Verify conservation
runner = NaryaProofRunner()
events = modelica_sim_to_narya(simulation_trajectory)
for e in events:
    runner.add_event(e)

bundle = runner.generate_proof_bundle()
assert bundle.overall == "VERIFIED"
assert bundle.verifiers["gf3_conservation"]["passed"]
```

## Assembly Index Integration

Validate molecular complexity of synthesis products:

```python
from assembly_index import compute_assembly_index

def validate_synthesis_complexity(target_smiles, max_complexity=20):
    """Ensure synthesis target has achievable complexity."""
    ai = compute_assembly_index(target_smiles)
    
    if ai > max_complexity:
        raise ValueError(f"Assembly index {ai} exceeds threshold {max_complexity}")
    
    return {
        "smiles": target_smiles,
        "assembly_index": ai,
        "synthesizable": ai <= max_complexity
    }
```

## Complete Pipeline Example

```python
#!/usr/bin/env python3
"""Chemputation pipeline: CRN → Modelica → XDL"""

from crn_topology import generate_reaction_network
from modelica_bridge import simulate_reaction, find_equilibrium
from turing_chemputer import compile_xdl
from narya_proofs import verify_trajectory

def chemputation_pipeline(target_smiles: str, conditions: dict):
    """Full chemputation pipeline with GF(3) triad."""
    
    # (+1) PLUS: Generate reaction network
    crn = generate_reaction_network(target_smiles)
    print(f"Generated CRN with {len(crn.species)} species, {len(crn.reactions)} reactions")
    
    # (0) ERGODIC: Simulate thermodynamics
    model = crn_to_modelica(crn)
    equilibrium = find_equilibrium(model, conditions)
    trajectory = simulate_reaction(model, t_max=100)
    print(f"Equilibrium: {equilibrium}")
    
    # (-1) MINUS: Execute synthesis
    xdl = modelica_to_xdl(equilibrium, conditions)
    hardware_plan = compile_xdl(xdl)
    print(f"XDL program: {len(xdl.steps)} steps")
    
    # Verify with narya-proofs
    proof = verify_trajectory(trajectory)
    assert proof.conserved, "GF(3) conservation violated!"
    
    return {
        "crn": crn,
        "equilibrium": equilibrium,
        "xdl": xdl,
        "proof": proof
    }

if __name__ == "__main__":
    result = chemputation_pipeline(
        target_smiles="CC(=O)OC1=CC=CC=C1C(=O)O",  # Aspirin
        conditions={"T": 80, "solvent": "acetic_anhydride"}
    )
```

## References

- Cronin Lab: https://www.chem.gla.ac.uk/cronin/
- XDL Specification: https://croningroup.gitlab.io/chemputer/xdl/
- AlgebraicPetri.jl: https://algebraicjulia.github.io/AlgebraicPetri.jl/
- Modelica Association: https://modelica.org
