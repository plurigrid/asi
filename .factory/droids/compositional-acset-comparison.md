---
name: compositional-acset-comparison
description: Compositional algorithm and data analysis via algebraic databases
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Compositional ACSet Comparison Skill

**Trit**: 0 (ERGODIC - Coordinator)
**Color**: #26D826 (Green)
**Domain**: Compositional algorithm/data analysis via algebraic databases

## Homoiconic Insight

In self-hosted Lisps, the boundary between data structures and algorithms dissolves:
- Code is data, data is code (homoiconicity)
- Evaluation time is phase-scoped (RED/BLUE/GREEN gadgets)
- Entanglement avoided by leaving phases open until explicitly closed
- Compositional structure preserved across algorithm ↔ data boundary

## Overview

Compare data structures and their properties (density/sparsity, dynamic/static, versioning strategies) using the richness afforded by ACSets. Uses Gay.jl-aided superrandom walks for deterministic exploration of comparison dimensions.

## Canonical Triads

```
schema-validation (-1) ⊗ compositional-acset-comparison (0) ⊗ gay-mcp (+1) = 0 ✓  [Property Analysis]
three-match (-1) ⊗ compositional-acset-comparison (0) ⊗ koopman-generator (+1) = 0 ✓  [Dynamic Traversal]
temporal-coalgebra (-1) ⊗ compositional-acset-comparison (0) ⊗ oapply-colimit (+1) = 0 ✓  [Versioning]
polyglot-spi (-1) ⊗ compositional-acset-comparison (0) ⊗ gay-mcp (+1) = 0 ✓  [Homoiconic Interop]
```

## Golden Thread Walk Dimensions

Each dimension is explored via φ-angle (137.508°) golden spiral for maximal dispersion:

| Step | Dimension | Hex Color | Hue |
|------|-----------|-----------|-----|
| 1 | Storage Hierarchy | #EE2B2B | 0° |
| 2 | Density/Sparsity | #2BEE64 | 137.51° |
| 3 | Dynamic/Static | #9D2BEE | 275.02° |
| 4 | Versioning Strategy | #EED52B | 52.52° |
| 5 | Traversal Patterns | #2BCDEE | 190.03° |
| 6 | Index Structures | #EE2B94 | 327.54° |
| 7 | Compression | #5BEE2B | 105.05° |
| 8 | Query Model | #332BEE | 242.55° |
| 9 | Embedding Support | #EE6C2B | 20.06° |
| 10 | Interoperability | #2BEEA5 | 157.57° |
| 11 | Concurrency | #DE2BEE | 295.08° |
| 12 | Memory Model | #C5EE2B | 72.59° |

## Comparison Matrix: DuckDB vs LanceDB

### Dimension 1: St