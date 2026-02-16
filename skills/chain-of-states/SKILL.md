# Chain of States (CoS) Skill 🐸

**Trit**: -1 (MINUS - Validator)
**GF(3) Triad**: `chain-of-states (-1) ⊗ proof-of-frog (0) ⊗ alife (+1) = 0`

## Overview

CoSProver framework for translating informal proofs to Lean4 via intermediate formal proof states.

From Wang et al. (2025): "Translating Informal Proofs into Formal Proofs Using a Chain of States"

## Core Insight

```
Informal Proof (natural language)
    ↓ Stage 1: Extract CoS
Chain of States [s₀ → s₁ → ... → sₙ]
    ↓ Stage 2: Generate tactics
Formal Lean4 Proof
```

**Key Observations**:
1. Informal proofs use logical transitions (implications/equivalences) without explicit intermediate states
2. Lean requires explicit proof states + tactics connecting them
3. CoS bridges this gap with explicit intermediate representations

## Two-Stage Framework

### Stage 1: CoS Extraction
```
"Let x > 0. Since x > 0, we have x² > 0."
    ↓
[⊢ x > 0 → x² > 0]  →  [h : x > 0 ⊢ x² > 0]  →  [⊢ True]
```

### Stage 2: Tactic Generation
```lean
theorem sq_pos (x : ℝ) (h : x > 0) : x² > 0 := by
  -- Tactic for s₀ → s₁
  intro h
  -- Tactic for s₁ → s₂  
  exact sq_pos_of_pos h
```

## Connection to Proof-of-Frog

| CoS Concept | Proof-of-Frog Equivalent |
|-------------|--------------------------|
| Proof state sᵢ | Knowledge nugget |
| Tactic τᵢ | Frog leap |
| State transition | Eating a frog |
| Full proof | Pond traversal |

### Frog Lifecycle as CoS

```
🥒 TADPOLE (s₀)     -- Initial goal state
    ↓ τ₁ (intro)
🐸 FROGLET (s₁)     -- Hypothesis introduced
    ↓ τ₂ (apply)
🦎 MATURE FROG (sₙ) -- QED
```

## Implementation

### Lean4 CoS Type
```lean
structure ProofState where
  goal : Expr
  context : List Expr
  trit : Int  -- GF(3) stage

structure ChainOfStates where
  states : List ProofState
  transitions : List Tactic
  
def cos_invariant (cos : ChainOfStates) : Prop :=
  (cos.states.map (·.trit)).sum % 3 = 0
```

### Python CoS Extraction
```python
def extract_cos(informal_proof: str) -> List[ProofState]:
    """
    Extract Chain of States from informal proof text.
    Each state is a formal representation of proof progress.
    """
    steps = segment_proof(informal_proof)
    return [formalize_state(s) for s in steps]
```

## Comparison to Chain-of-Thought

| Dimension | Chain-of-Thought (CoT) | Chain of States (CoS) |
|-----------|------------------------|------------------------|
| Target | Reasoning trace | Proof states |
| Granularity | Natural language | Formal expressions |
| Verification | None | Lean type checker |
| Composability | Weak | Strong (tactic composition) |

## Performance (Wang et al. 2025)

| Benchmark | miniF2F | ProofNet |
|-----------|---------|----------|
| Direct generation | 36.2% | 18.4% |
| **CoSProver** | **42.8%** | **24.1%** |
| Improvement | +6.6% | +5.7% |

## Usage

```bash
# Load skill
skill chain-of-states

# Extract CoS from informal proof
python cos_extract.py "Let n be even. Then n² is even."

# Generate Lean4 tactics
lean4 cos_to_tactics.lean
```

## References

- Wang et al. (2025). "Translating Informal Proofs into Formal Proofs Using a Chain of States." [arXiv:2512.10317](https://arxiv.org/abs/2512.10317)
- Ahuja et al. (2024). "ImProver: Agent-Based Automated Proof Optimization" - Chain-of-States technique. [arXiv:2410.04753](https://arxiv.org/abs/2410.04753)

## Либиди Фрог Connection

**Либиди Фрог** (Proof-of-Frog) + **Chain of States** = compositional proof verification:

```
proof-chain(-1) ⊗ proof-of-frog(0) ⊗ alife(+1) = 0 ✓

Where Chain of States provides the -1 (validator) role:
- Validates each state transition
- Ensures GF(3) conservation across proof steps
- Connects informal human reasoning to formal verification
```

## Gay.jl Colors

```julia
using Gay
seed = gay_seed(2512)  # arXiv paper ID
palette(3)  # CoS triad colors
```

| Stage | Color | Meaning |
|-------|-------|---------|
| Initial | `#B0285F` | Unproven goal |
| Intermediate | `#77DEB1` | Progress state |
| Terminal | `#8ADB6E` | QED |


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
