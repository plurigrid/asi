---
name: gf3-tripartite
description: GF(3) Tripartite Orchestration
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# GF(3) Tripartite Orchestration

A skill for coordinating multi-agent systems using GF(3) (Galois Field of 3 elements) conservation. Implements the core pattern: **local choice χ ∈ {-1, 0, +1} determines all state transitions**.

## Description

This skill enables agents to:
- Assign trit values (-1, 0, +1) to operations and entities
- Verify GF(3) conservation: Σχ ≡ 0 (mod 3)
- Coordinate triadic agent compositions
- Map operations to deterministic colors via Gay.jl

## Usage

### Trit Assignment

When orchestrating multiple agents or operations, assign trits:

| Trit | Role | Semantics |
|------|------|-----------|
| **+1** (PLUS) | Generator | Create, advance, produce |
| **0** (ERGODIC) | Transformer | Process, maintain, equilibrate |
| **-1** (MINUS) | Absorber | Consume, validate, verify |

### Conservation Check

For any triplet of operations to compose correctly:
```
trit(A) + trit(B) + trit(C) ≡ 0 (mod 3)
```

Valid triplets:
- (+1, +1, +1) → 3 ≡ 0 ✓
- (+1, 0, -1) → 0 ≡ 0 ✓
- (+1, -1, 0) → 0 ≡ 0 ✓
- (0, 0, 0) → 0 ≡ 0 ✓
- (-1, -1, +1) → -1 ≡ 0? → -1 + 3 = 2 ✗ (invalid!)

### Example: ALIFE Structural Diffing

Three orthogonal vectors for change:

| Vector | Type | Trit | Description |
|--------|------|------|-------------|
| α | Behavioral/State | 0 (ERGODIC) | Time evolution within fixed ontology |
| β | Structural/Type | +1 (PLUS) | Mutation of code, morphology, parameters |
| γ | Bridge/Coherence | -1 (MINUS) | Meta-layer mapping structure to function |

Sum: α(0) + β(+1) + γ(-1) = 0 ✓

## Applications

### Multi-Agent Coordination

```
Agent A (Explorer, +1)    - generates new possibilities
Agent B (Processor, 0)    - transforms and routes
Agent C (Validator, -1)   - verifies and absorbs

Σ = +1 + 0 + (-1) = 0 ✓
```

### World-Hopping (Counterfactual Navigation)

```
World-Hopping (+1)        - explore parallel worlds
Triad-Interleave (0)      - weave between possibilities
Epistemic-Arbitrage (-1)  - exploit knowledge differentials

Σ = 0 ✓
```

### Cat