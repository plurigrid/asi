---
name: datalog-fixpoint
description: Datalog bottom-up fixpoint iteration for recursive queries
version: 1.0.0
---


# Datalog Fixpoint Skill

Bottom-up fixpoint iteration for recursive Datalog queries without explicit recursion.

## Core Concept

Datalog computes fixpoints via iterative saturation:
```
T^0(∅) → T^1 → T^2 → ... → T^ω (fixpoint)
```

Where T is the immediate consequence operator.


## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Dataframes
- **polars** [○] via bicomodule
  - High-performance dataframes

### Bibliography References

- `algorithms`: 19 citations in bib.duckdb



## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 3. Variations on an Arithmetic Theme

**Concepts**: generic arithmetic, coercion, symbolic, numeric

### GF(3) Balanced Triad

```
datalog-fixpoint (+) + SDF.Ch3 (○) + [balancer] (−) = 0
```

**Skill Trit**: 1 (PLUS - generation)


### Connection Pattern

Generic arithmetic crosses type boundaries. This skill handles heterogeneous data.
## Cat# Integration

Fixpoint computation maps to Cat# via coalgebraic semantics:

```
Trit: 0 (ERGODIC - iterative bridge)
Home: Prof (profunctors/bimodules)
Poly Op: ⊗ (parallel saturation)
Kan Role: Adj (Kleisli adjunction)
```

### GF(3) Naturality

Datalog fixpoint iteration is inherently ERGODIC:
- Each iteration step is a natural transformation
- Convergence = reaching the terminal coalgebra
- The fixpoint IS the bicomodule equilibrium