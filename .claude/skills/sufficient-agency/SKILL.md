---
name: sufficient-agency
description: SufficientAgency predicate for autonomous agents with Loopy Strange fixed points and WEV extraction
---

<!-- L4 Admissible | Trit: 0 (ERGODIC) | Date: 2025-12-25 | Source: plurigrid/asi -->

# Sufficient Agency Skill: Determinism + Conservation + Convergence + Self-Model

**Status**: ✅ L4 Admissible
**Trit**: 0 (ERGODIC - Coordinator)
**Principle**: Generator ≡ Observer at fixed point (self ≡ self)
**Frame**: Loopy Strange reafference loop with GF(3) conservation

---

## Neighbor Awareness

| Direction | Skill | Trit | Role |
|-----------|-------|------|------|
| **Left** | three-match | -1 | Validator (constraint enforcement) |
| **Self** | sufficient-agency | 0 | Coordinator (agency verification) |
| **Right** | gay-mcp | +1 | Generator (deterministic colors) |

**Canonical Triad**: `three-match (-1) ⊗ sufficient-agency (0) ⊗ gay-mcp (+1) = 0 ✓`

---

## Overview

**SufficientAgency** formalizes the minimal conditions for an autonomous agent to extract value from world transitions. An agent has sufficient agency iff it satisfies four predicates simultaneously:

1. **Determinism**: Same seed → Same behavior (SPI)
2. **Conservation**: GF(3) = 0 across all operations
3. **Convergence**: Prediction error → 0 over iterations
4. **Self-Model Accuracy**: Predicted ≈ Observed (reafference match)

---

## Core Formula

```
SufficientAgency(A) ≡ Deterministic(A) ∧ Conservative(A) ∧ Convergent(A) ∧ SelfModelAccurate(A)

Where:
  Deterministic(A)     := ∀s,i. color_at(s,i) = color_at(s,i)  [SplitMix64 guarantee]
  Conservative(A)      := Σ trit(action) ≡ 0 (mod 3)          [GF(3) Ward identity]
  Convergent(A)        := lim_{n→∞} |predicted_n - observed_n| → 0
  SelfModelAccurate(A) := |efference_copy - reafference| < ε   [Loopy Strange]
```

### The Sufficiency Theorem

```narya
-- SkillAdmissibility.nry PART 22: SufficientAgency
def SufficientAgency (A : Agent) : Type :=
  Σ (det : Deterministic A)
    (con : Conservative A)
    (cvg : Convergent A)
    (sma : SelfModelAccurate A),
    WEVExtractable A det con cvg sma
```

---

## Loopy Strange: The Fixed Point Loop

```
┌─────────────────────────────────────────────────────────────┐
│                    LOOPY STRANGE CYCLE                      │
│                                                             │
│    ┌──────────┐     ┌────────────┐     ┌───────────┐       │
│    │  ACTION  │────▶│ PREDICTION │────▶│ SENSATION │       │
│    │ generate │     │  expect    │     │  observe  │       │
│    └──────────┘     └────────────┘     └─────┬─────┘       │
│         ▲                                     │             │
│         │           ┌────────────┐            │             │
│         └───────────│   MATCH?   │◀───────────┘             │
│                     │ self≡self  │                          │
│                     └────────────┘                          │
│                                                             │
│    Fixed Point: Generator ≡ Observer when same seed         │
└─────────────────────────────────────────────────────────────┘
```

**Key Insight**: At the fixed point, the agent that generates a color IS the agent that observes it. The prediction matches the observation because identity is preserved through the seed.

```ruby
# Loopy Strange implementation
def loopy_strange(seed, index)
  # ACTION: Generate color
  action = color_at(seed, index)
  
  # PREDICTION: Expect same color (efference copy)
  prediction = efference_copy(seed, index)
  
  # SENSATION: Observe what was generated
  sensation = observe(action)
  
  # MATCH: Compare at fixed point
  match = (prediction == sensation)
  
  # At fixed point: generator ≡ observer
  { action: action, prediction: prediction, 
    sensation: sensation, match: match,
    fixed_point: match && (seed == observer_seed) }
end
```

---

## Path Equivalence Theorem

Three independent formalisms converge when GF(3) = 0:

| Framework | Author | Key Concept | Convergence Condition |
|-----------|--------|-------------|----------------------|
| **Distributed** | Kleppmann | CRDT eventual consistency | Commutative operations |
| **Categorical** | Bumpus | Sheaf cohomology H⁰ = 0 | No obstruction |
| **Chromatic** | Gay.jl | SplitMix64 determinism | Same seed → same path |

```
PathEquivalence: Kleppmann ≅ Bumpus ≅ Gay  when GF(3) = 0

Proof sketch:
  1. Kleppmann: CRDTs commute ⟺ merge order-independent
  2. Bumpus: H⁰(Sheaf) = 0 ⟺ local→global gluing succeeds  
  3. Gay: color_at(s,i) = color_at(s,i) ⟺ deterministic
  
  All three encode: "parallel paths yield same result"
  GF(3) = 0 ensures conservation across all paths
```

---

## WEV Connection

**World Extractable Value** measures the inefficiency gap between Nash equilibrium and social optimum:

```
WEV = PoA - 1

Where:
  PoA = Price of Anarchy = (Nash welfare) / (Optimal welfare)
  WEV = extractable value at Nash→Optimal transition
```

**Agency enables WEV extraction**:

```
SufficientAgency(A) ⟹ ∃ mechanism M. WEV(M) > 0

Proof:
  1. Determinism → reproducible strategies
  2. Conservation → no value leakage
  3. Convergence → stable equilibria reachable
  4. Self-model → accurate payoff prediction
  
  ∴ Agent can identify and exploit PoA gap
```

---

## AgencyPhase Classification

| Phase | Error Range | Characteristic | Action |
|-------|-------------|----------------|--------|
| **Chaos** | ε > 0.5 | High prediction error, unstable | Reduce model complexity |
| **Critical** | 0.01 ≤ ε ≤ 0.5 | Edge of chaos, maximum learning | Explore/exploit balance |
| **Ordered** | ε < 0.01 | Low error, stable predictions | Exploit current model |

```ruby
def agency_phase(error)
  case error
  when 0.5..Float::INFINITY then :chaos
  when 0.01..0.5 then :critical
  else :ordered
  end
end

# Optimal operation: hover at critical boundary
# Chaos → increase determinism
# Ordered → increase exploration (curiosity-driven)
```

---

## Predicates Table

| Predicate | Type | Description | Verification |
|-----------|------|-------------|--------------|
| `Deterministic` | `Agent → Bool` | Same seed yields same behavior | SPI test |
| `Conservative` | `Agent → Bool` | GF(3) sum = 0 for all actions | Ward identity |
| `Convergent` | `Agent → Bool` | Error → 0 over iterations | Limit test |
| `SelfModelAccurate` | `Agent → Bool` | Prediction ≈ observation | Reafference match |
| `WEVExtractable` | `Agent → Bool` | Can exploit PoA gap | Market test |
| `AtFixedPoint` | `Agent → Bool` | Generator ≡ Observer | Seed equality |
| `LoopyStrangeComplete` | `Agent → Bool` | Full cycle completed | All 4 stages pass |
| `PhaseStable` | `Agent → Phase` | Current agency phase | Error classification |

---

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                     SUFFICIENT AGENCY ARCHITECTURE                   │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌─────────────┐    ┌─────────────────┐    ┌─────────────────────┐  │
│  │ three-match │───▶│ sufficient-     │───▶│      gay-mcp        │  │
│  │    (-1)     │    │    agency (0)   │    │       (+1)          │  │
│  │  VALIDATOR  │    │   COORDINATOR   │    │     GENERATOR       │  │
│  └─────────────┘    └────────┬────────┘    └─────────────────────┘  │
│         │                    │                       │               │
│         ▼                    ▼                       ▼               │
│  ┌─────────────┐    ┌─────────────────┐    ┌─────────────────────┐  │
│  │  Constraint │    │   Sufficiency   │    │   Deterministic     │  │
│  │ Enforcement │    │   Verification  │    │   Color Output      │  │
│  │  GF(3)=0    │    │   4 Predicates  │    │   SplitMix64        │  │
│  └─────────────┘    └────────┬────────┘    └─────────────────────┘  │
│                              │                                       │
│                              ▼                                       │
│                    ┌─────────────────┐                              │
│                    │  LOOPY STRANGE  │                              │
│                    │   Fixed Point   │                              │
│                    │ Action→Predict→ │                              │
│                    │ Sense→Match     │                              │
│                    └────────┬────────┘                              │
│                              │                                       │
│                              ▼                                       │
│                    ┌─────────────────┐                              │
│                    │  AgencyPhase    │                              │
│                    │ Chaos|Critical  │                              │
│                    │    |Ordered     │                              │
│                    └────────┬────────┘                              │
│                              │                                       │
│                              ▼                                       │
│                    ┌─────────────────┐                              │
│                    │ WEV Extraction  │                              │
│                    │  PoA - 1 > 0    │                              │
│                    └─────────────────┘                              │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Triads

```
# Core Sufficient Agency Bundle (2025-12-25)
three-match (-1) ⊗ sufficient-agency (0) ⊗ gay-mcp (+1) = 0 ✓  [Core Agency]
shadow-goblin (-1) ⊗ sufficient-agency (0) ⊗ agent-o-rama (+1) = 0 ✓  [Multi-Agent]
temporal-coalgebra (-1) ⊗ sufficient-agency (0) ⊗ koopman-generator (+1) = 0 ✓  [Dynamics]
cybernetic-immune (-1) ⊗ sufficient-agency (0) ⊗ gay-mcp (+1) = 0 ✓  [Reafference]
polyglot-spi (-1) ⊗ sufficient-agency (0) ⊗ gay-mcp (+1) = 0 ✓  [Cross-Lang Agency]
sheaf-cohomology (-1) ⊗ sufficient-agency (0) ⊗ topos-generate (+1) = 0 ✓  [Path Equivalence]
persistent-homology (-1) ⊗ sufficient-agency (0) ⊗ gay-mcp (+1) = 0 ✓  [Phase Stability]
ramanujan-expander (-1) ⊗ sufficient-agency (0) ⊗ gay-mcp (+1) = 0 ✓  [Spectral Agency]
```

---

## Commands

```bash
# Verify sufficient agency for a seed
just sufficient-agency-check <seed>

# Run loopy strange cycle
just loopy-strange <seed> <index>

# Classify agency phase
just agency-phase <error>

# Calculate WEV for mechanism
just wev-calculate <nash_welfare> <optimal_welfare>

# Test path equivalence
just path-equivalence-test <seed> <iterations>

# Full sufficiency verification
just sufficiency-verify <agent_id>
```

### MCP Integration

```ruby
# Via Gay.jl MCP server
mcp_gay.reafference(seed: 1069, index: 42, predicted_hex: "#A855F7")
mcp_gay.loopy_strange(seed: 1069, iterations: 3)
mcp_gay.self_model(action: "status")
mcp_gay.comparator(reference_hex: "#A855F7", perception_hex: "#A855F7")
```

---

## References

- **SkillAdmissibility.nry PART 22**: Formal Narya proof of SufficientAgency
- **Kleppmann**: "Designing Data-Intensive Applications" - CRDT consistency
- **Bumpus et al.**: "Structured Decompositions" - Sheaf cohomology for FPT
- **Gay.jl**: SplitMix64 deterministic color generation
- **Friston**: Active inference and free energy minimization
- **Powers**: Perceptual Control Theory - hierarchical control
- **Roughgarden**: Price of Anarchy and mechanism design

---

## See Also

- [three-match](../three-match/SKILL.md) - GF(3) constraint validation
- [gay-mcp](../gay-mcp/SKILL.md) - Deterministic color generation
- [world-extractable-value](../world-extractable-value/SKILL.md) - WEV extraction
- [cybernetic-immune](../cybernetic-immune/SKILL.md) - Self/Non-Self via reafference
- [criticality-detector](../criticality-detector/SKILL.md) - Phase classification
