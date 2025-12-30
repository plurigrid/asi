# Cybernetic Immune Skill

> *"Self/Non-Self discrimination via reafference, GF(3) trit encoding, and information geometry."*

## Overview

**Cybernetic Immune** implements a self-modifying immune system combining:
- Varela's autopoietic self-organization
- Friston's free energy principle
- Powers' perceptual control theory

The system discriminates Self from Non-Self through reafference matching.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | 0 (ERGODIC) |
| Role | COORDINATOR |
| Function | Mediates between self-recognition and threat detection |

## Core Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                  CYBERNETIC IMMUNE SYSTEM                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│    ┌──────────────┐                    ┌──────────────┐         │
│    │    SELF      │                    │   NON-SELF   │         │
│    │  (Familiar)  │◄──── Boundary ────►│  (Foreign)   │         │
│    │  trit: +1    │                    │  trit: -1    │         │
│    └──────────────┘                    └──────────────┘         │
│            │                                  │                 │
│            └──────────┬───────────────────────┘                 │
│                       │                                         │
│                       ▼                                         │
│              ┌────────────────┐                                 │
│              │  COORDINATOR   │                                 │
│              │   (Boundary)   │                                 │
│              │   trit: 0      │                                 │
│              └────────────────┘                                 │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Reafference Discrimination

From von Holst's reafference principle:

```python
class ReafferenceDiscriminator:
    """
    Distinguish self-caused from externally-caused sensations.

    reafference = sensation caused by own action
    exafference = sensation caused by external source
    """

    def __init__(self, seed: int):
        self.efference_copy = {}  # Predicted sensations
        self.seed = seed

    def predict_sensation(self, action: Action) -> Sensation:
        """Generate efference copy (expected reafference)."""
        return self.forward_model(action, self.seed)

    def classify(self, action: Action, sensation: Sensation) -> str:
        """Classify sensation as Self or Non-Self."""
        predicted = self.predict_sensation(action)

        if sensation == predicted:
            return "SELF"  # Reafference - we caused this
        else:
            return "NON-SELF"  # Exafference - external cause
```

## Free Energy Minimization

```python
class FristonImmune:
    """
    Minimize free energy to maintain self-organization.

    F = D_KL(q(θ) || p(θ|data)) + log p(data)

    Low F = good model of self
    High F = potential threat (model violation)
    """

    def free_energy(self, observation, model):
        """Compute variational free energy."""
        # Prediction error (surprise)
        prediction = model.predict()
        error = kl_divergence(observation, prediction)

        # Complexity (model size)
        complexity = model.complexity()

        return error + complexity

    def respond(self, observation):
        """Immune response based on free energy."""
        F = self.free_energy(observation, self.self_model)

        if F < self.threshold:
            return "TOLERATE"  # Low surprise = self-like
        else:
            return "ATTACK"  # High surprise = foreign
```

## GF(3) Trit Encoding

```python
class TriadicImmune:
    """
    Encode immune states in GF(3).
    """

    SELF = +1      # Recognized as self
    BOUNDARY = 0   # Under evaluation
    NON_SELF = -1  # Recognized as foreign

    def classify_antigen(self, antigen):
        """Assign GF(3) trit to antigen."""
        self_similarity = self.compute_similarity(antigen, self.self_model)

        if self_similarity > 0.8:
            return self.SELF
        elif self_similarity < 0.2:
            return self.NON_SELF
        else:
            return self.BOUNDARY  # Needs further evaluation

    def conservation_check(self, population):
        """Verify GF(3) conservation across immune population."""
        trit_sum = sum(cell.trit for cell in population)
        return trit_sum % 3 == 0
```

## Perceptual Control (Powers)

```python
class PowersImmune:
    """
    Control perception of self-integrity.

    The immune system controls what it perceives (health),
    not what it does (specific responses).
    """

    def __init__(self, reference_state):
        self.reference = reference_state  # Desired health
        self.gain = 0.8

    def control_loop(self, perception):
        """PCT control loop for immune regulation."""
        error = self.reference - perception
        output = self.gain * error

        if error > 0:
            # Perception below reference - upregulate
            return ("UPREGULATE", output)
        else:
            # Perception above reference - downregulate
            return ("DOWNREGULATE", -output)
```

## GF(3) Triads

```
cybernetic-immune (0) ⊗ reafference-corollary-discharge (+1) ⊗ dynamic-sufficiency (-1) = 0 ✓
cybernetic-immune (0) ⊗ self-validation-loop (+1) ⊗ fokker-planck-analyzer (-1) = 0 ✓
```

## Integration with Gay.jl

```python
# Deterministic color coding for immune states
from gay import color_at

def visualize_immune_state(cell, seed=0x42D):
    """Color code immune cell by GF(3) state."""
    color = color_at(cell.id, seed=seed)

    if cell.trit == +1:
        return (color, "SELF", "green")
    elif cell.trit == 0:
        return (color, "BOUNDARY", "yellow")
    else:
        return (color, "NON_SELF", "red")
```

---

**Skill Name**: cybernetic-immune
**Type**: Self-Organization / Immune Systems
**Trit**: 0 (ERGODIC - COORDINATOR)
**GF(3)**: Mediates Self/Non-Self boundary
