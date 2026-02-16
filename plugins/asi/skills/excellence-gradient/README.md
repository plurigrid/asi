# Excellence Gradient Skill

> *"Reject mediocrity. Follow the gradient toward excellence. Ship or die."*

## Overview

**Excellence Gradient** implements quality-driven development with continuous improvement metrics. Every iteration should move up the gradient toward excellence.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | +1 (PLUS) |
| Role | GENERATOR |
| Function | Generates improvements along the excellence gradient |

## The Gradient

```
Excellence
    ▲
    │    ★ Target
    │   /
    │  /  gradient
    │ /   direction
    │/
    ●────────────────► Iterations
  Current
  State
```

## Core Metrics

```python
class ExcellenceMetrics:
    """Measure progress along the excellence gradient."""

    def __init__(self):
        self.history = []

    def measure(self, artifact):
        """Compute excellence score for an artifact."""
        return {
            'correctness': self.test_pass_rate(artifact),
            'performance': self.benchmark_score(artifact),
            'clarity': self.readability_score(artifact),
            'simplicity': self.complexity_inverse(artifact),
            'coverage': self.test_coverage(artifact),
        }

    def gradient(self, current, previous):
        """Compute improvement gradient."""
        return {
            k: current[k] - previous.get(k, 0)
            for k in current
        }

    def is_improving(self, current, previous):
        """Check if we're moving up the gradient."""
        grad = self.gradient(current, previous)
        return sum(grad.values()) > 0
```

## Excellence Principles

### 1. Refuse Mediocrity

```python
def review_pr(pr):
    """Reject PRs that don't meet excellence bar."""
    metrics = measure(pr)

    if metrics['correctness'] < 1.0:
        return Reject("Tests must pass")

    if metrics['simplicity'] < 0.7:
        return Reject("Too complex - simplify")

    if metrics['clarity'] < 0.8:
        return Reject("Needs better documentation")

    return Approve("Meets excellence bar")
```

### 2. Demand Excellence

```python
def demand_excellence(team):
    """Set and enforce high standards."""
    standards = {
        'code_review': "Every line reviewed",
        'testing': "100% critical path coverage",
        'documentation': "API fully documented",
        'performance': "P99 < 100ms",
    }

    for standard, requirement in standards.items():
        if not meets_standard(team, standard):
            raise StandardNotMet(f"{standard}: {requirement}")
```

### 3. Ship or Die

```python
def ship_or_die(feature, deadline):
    """Excellence without shipping is worthless."""
    while not feature.shipped and now() < deadline:
        # Find highest-impact improvement
        improvements = prioritize_by_impact(feature.todos)

        # Execute top improvement
        if improvements:
            execute(improvements[0])
        else:
            break

    if not feature.shipped:
        # Scope down to what can ship
        feature.scope = minimum_viable(feature)

    ship(feature)  # Always ship something
```

## GF(3) Excellence Triads

```python
class ExcellenceTriad:
    """
    Excellence requires all three GF(3) roles:
    - GENERATOR (+1): Create excellent work
    - COORDINATOR (0): Integrate and balance
    - VALIDATOR (-1): Verify excellence maintained
    """

    def iterate(self, artifact):
        # Generate improvement
        improved = self.generator.improve(artifact)  # +1

        # Coordinate integration
        integrated = self.coordinator.merge(improved)  # 0

        # Validate excellence
        if self.validator.verify(integrated):  # -1
            return integrated
        else:
            return self.iterate(integrated)  # Recurse until excellent

        # Net: +1 + 0 + (-1) = 0 ✓
```

## Gradient Descent to Excellence

```python
def excellence_gradient_descent(artifact, target_score=0.95):
    """Follow gradient toward excellence."""
    current = artifact
    score = measure(current)['overall']

    while score < target_score:
        # Compute gradient
        grad = compute_gradient(current)

        # Step in direction of steepest improvement
        current = apply_improvement(current, grad)

        # Re-measure
        score = measure(current)['overall']
        print(f"Score: {score:.2%}")

    return current
```

## Commands

```bash
# Measure excellence
just excellence-measure src/

# Check gradient direction
just excellence-gradient --compare HEAD~1

# Enforce standards
just excellence-enforce --strict
```

## GF(3) Triads

```
excellence-gradient (+1) ⊗ code-review (0) ⊗ qa-regression (-1) = 0 ✓
excellence-gradient (+1) ⊗ cognitive-superposition (0) ⊗ system2-attention (-1) = 0 ✓
```

---

**Skill Name**: excellence-gradient
**Type**: Quality Engineering
**Trit**: +1 (PLUS - GENERATOR)
**GF(3)**: Generates improvements toward excellence
