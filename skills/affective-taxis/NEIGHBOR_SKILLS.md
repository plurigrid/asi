# Affective-Taxis Neighbor Skills

**Date**: 2026-02-11
**Framework**: GF(3) Neighborhood Awareness
**Paper**: Sennesh & Ramstead 2025, arXiv:2505.17024

---

## Tier 1: Core Concomitant Skills

| Skill | Trit | Role | Interface | Morphism |
|-------|------|------|-----------|----------|
| **langevin-dynamics** | 0 | SDE analysis | Navigation = Bayesian inference | `langevin_to_taxis()` |
| **fokker-planck-analyzer** | +1 | Stationary dist | Equilibrium of energy landscape | `prove_convergence()` |
| **modelica** | 0 | DAE formulation | Circuit/physical analogy | `dae_to_energy_landscape()` |
| **open-games** | +1 | Multi-agent clearing | Compositional game (Hedges) | `clearing_to_game()` |
| **persistent-homology** | -1 | Topological signal | Sublevel filtration of E(z) | `persistence_to_gf3()` |
| **gf3-tripartite** | 0 | Conservation | Structural invariant verification | `verify_gf3_conservation()` |

**GF(3) Check**: (-1) + (0) + (+1) + (0) + (+1) + (-1) + (0) = 0

---

## Tier 2: BCI-Phenomenal Bridge

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **crossmodal-gf3** | 0 | Sensory integration | FCD across modalities |
| **active-inference-robotics** | +1 | Robot control | Langevin → UR5 commands |
| **entropy-sim2real** | -1 | Transfer | Sim energy → real energy |

**Triplet**: Affective-Taxis ⊗ Active-Inference-Robotics ⊗ Entropy-Sim2Real

---

## Tier 3: Market/Clearing

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **cybernetic-open-game** | +1 | Game structure | Multi-agent as open game |
| **taxis_clearing.py** | 0 | Implementation | Newton/CoW preserve GF(3) |
| **accept-no-substitutes** | -1 | Validation | Only atomic methods pass |

**Key finding**: Only Newton and CoW batch auction preserve GF(3) conservation.
GD and EIP-1559 break the structural invariant.

---

## Tier 4: Causal Structure

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **indefinite-causal-order** | 0 | Generalized taxis | Valence→ICO control mapping |
| **time-travel-crdt** | -1 | Temporal order | Indefinite merge order |
| **zx-calculus** | +1 | Circuit structure | ZX diagram of taxis→ICO |

**Key bridge**: Valence ≈ 0 → agent enters indefinite causal order with its
environment (neither sense→act nor act→sense is definite).

---

## Integration Paths

### Path A: Modelica Triplet #3
```
Modelica DAE → Langevin SDE → Affective Taxis
  (landscape)     (navigation)    (valence/GF(3))
```
Extends Triplet #2 with affective valence classification.

### Path B: BCI Pipeline
```
EEG → Fisher-Rao → Phenomenal State → Taxis → Robot
  (Bridge 9 Phase 1-4)                  (this skill)
```
FCD signal from phenomenal field drives robot navigation.

### Path C: Market Alignment
```
Agent positions → Shared landscape → Clearing → GF(3) check
  (taxis_clearing.py)               (Newton/CoW)
```
Multi-agent alignment theorem: shared landscape + GF(3) = aligned.

### Path D: Indefinite Causal Order
```
Valence → ICO Control → Quantum Switch → Channel Transform
  (FCD)     (trit)       (supermap.zig)    (phase cell output)
```
When valence ≈ 0, the agent enters genuinely indefinite causal order:
the sense→act ordering is no longer fixed. Maps to process matrix formalism.
