# Indefinite Causal Order: Neighbor Skills

## Tier 1: Core Triad

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **gf3-tripartite** | +1 | Conservation proof | `verify_gf3_conservation(switch_outputs)` |
| **indefinite-causal-order** | 0 | Coordination | `quantum_switch(C1, C2, control)` |
| **affective-taxis** | -1 | Validation via landscape | `taxis_ico_bridge(valence)` |

GF(3) check: (+1) + (0) + (-1) = 0

## Tier 2: Structural Neighbors

| Skill | Trit | Interface | Morphism |
|-------|------|-----------|----------|
| **zx-calculus** | +1 | ZX diagram of quantum switch | `ico_to_zx(C1, C2, control)` |
| **open-games** | +1 | Nash over ICO strategies | `ico_game(strategies, process_matrix)` |
| **time-travel-crdt** | -1 | Indefinite temporal order for CRDTs | `crdt_ico_merge(state1, state2)` |
| **langevin-dynamics** | -1 | Stochastic process on ICO space | `langevin_on_process_matrix(W, dt)` |
| **captp** | 0 | OCapN capabilities as affordance-gated supermaps | `affordance_to_capability(aff)` |
| **autopoiesis** | 0 | Self-referential causal order | `autopoietic_switch(self_channel)` |

## Tier 3: Implementation Substrates

| Substrate | File | What it provides |
|-----------|------|-----------------|
| **Zig** | `zig-syrup/src/supermap.zig` | Channel, Supermap, quantumSwitch, PhaseCell, CyberPhysical, C ABI |
| **Zig** | `zig-syrup/src/unworld.zig` | Fractal causal chain operads (7 levels), AellithPrim |
| **Zig** | `zig-syrup/src/entangle.zig` | CNOT₃ qutrit gate, Trit arithmetic |
| **Zig** | `zig-syrup/src/disclosure.zig` | OSI-like disclosure with supermaps |
| **Hy/Python** | `hymlx/src/hymlx/transforms_ico.hy` | ICOContext, ProcessMatrix, ico-lift/compose/parallel/switch/triad |
| **Julia** | `indefinite_causal_order.jl` | Process matrices, causal witnesses, CyberPhysical loop |
| **Modelica** | via `affective_taxis.mo` | DAE energy landscape with ICO control |

## Active Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| **ICO Core** | ICO ⊗ GF3-Tripartite ⊗ Affective-Taxis | Causal order conservation |
| **ICO Dynamics** | ICO ⊗ Langevin ⊗ ZX-Calculus | Stochastic quantum circuits |
| **ICO Games** | ICO ⊗ Open-Games ⊗ Time-Travel-CRDT | Strategic indefinite order |
