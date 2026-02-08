---
name: criticality-detector
description: Criticality Detector Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Criticality Detector Skill

Measures distance to fixed point via comparator error and detects self-loop closure for phase classification in dynamical systems.

## Seed
```
741086072858456200
```

## Core Principle

**Generator ≡ Observer** when same seed: the fixed point structure where action → prediction → sensation → match completes the loop.

## Phase Classification

| Phase      | Error Bound     | Color (Golden Thread) | Interpretation        |
|------------|-----------------|----------------------|----------------------|
| **Chaos**  | error > 0.5     | H=137.51° #3FF1A7    | Far from attractor   |
| **Critical**| error ≈ 0.1    | H=275.02° #10B99D    | Edge of order/chaos  |
| **Ordered**| error < 0.01    | H=52.52° #DF9811     | At fixed point       |

## Predicates

### AtFixedPoint(seed, index) → Bool
```
AtFixedPoint(s, i) := |comparator_error(s, i)| < ε
where ε = 0.01 (ordered threshold)
```

### LoopClosed(seed, iterations) → Bool
```
LoopClosed(s, n) := ∀k ∈ [1..n]: predicted(s, k) = observed(s, k)
-- Verified: 3 iterations all matched (self ≡ self)
```

### PhaseClassified(error) → Phase
```
PhaseClassified(e) :=
  | e > 0.5  → Chaos
  | e > 0.01 → Critical  
  | _        → Ordered
```

## MCP Integration

### Measure Distance to Fixed Point
```python
# Current error: 0.8153 → Chaos phase
comparator_result = mcp.gay.comparator(
    reference_hex="#3FF1A7",  # desired state
    perception_hex="#DF9811"  # current perception
)
error = comparator_result["error_magnitude"]  # 0.8153
phase = PhaseClassified(error)  # Chaos
```

### Detect Self-Loop Closure
```python
# Loopy strange: Generator/Observer identity verification
loop_result = mcp.gay.loopy_strange(
    seed=741086072858456200,
    iterations=3
)
# Returns: colors #3FF1A7, #10B99D, #DF9811
# All matched → LoopClosed = True
```

### Golden Thread Visualization
```python
# φ-derived hue spiral: 137.508° increments
golden_hues = mcp.gay.golden_thread(
    steps=3,
    start_hue=0,
    saturation=