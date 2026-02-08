---
name: topos-adhesive-rewriting
description: Adhesive categories for incremental query updating and pattern rewriting
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# SKILL: Topos Adhesive Rewriting

**Version**: 1.0.0
**Trit**: +1 (PLUS)
**Domain**: category-theory, rewriting, databases, incremental-computation
**Source**: Topos Institute Blog (Kris Brown)

---

## Overview

Adhesive categories provide a **general setting for pattern matching and rewriting** where pushouts along monomorphisms behave well. This skill covers:

1. **Incremental Query Updating** - Efficiently update query results when queried object changes
2. **Decompositions** - Q ≅ Q_G +_{Q_L} Q_R factorization
3. **Interactions** - Pullback squares between pattern subobjects and rewrite rules
4. **Rooted Search** - Transform subgraph isomorphism into rooted search problems
5. **Complements** - ∼A is smallest subobject where X = A ∨ ∼A

---

## Core Concept: The Incremental Search Problem

```
   Query Q          Old State G          New State H
  ┌───────┐        ┌───────────┐        ┌───────────┐
  │ a→b→c │   Hom  │  1 → 2 ↺  │   Δ    │  1→2↺     │
  └───────┘  ───→  └───────────┘  ───→  │   ↘3↙    │
                    matches:             └───────────┘
                    [1,2,2]              new matches:
                    [2,2,2]              [1,3,2], [3,2,2]
```

**Goal**: Compute `Hom(Q,H) \ Hom(Q,G)·Δ` efficiently without recomputing from scratch.

---

## Dictionary: Category Theory ↔ Computation

| Setting | Category Theory |
|---------|-----------------|
| Pattern/Query | Object Q ∈ Ob C |
| State of world | Object G ∈ Ob C |
| Pattern match | Morphism Q → G |
| Answer set | Hom_C(Q, G) |
| Additive rewrite rule | Monomorphism f: L ↣ R |
| Rule application | Pushout G →^Δ H ←^r R |

---

## The Adhesive Cube

For any match h: Q → H into a rewrite result, adhesivity gives a canonical decomposition:

```
           Q ≅ Q_R +_{Q_L} Q_G
              ╱     │     ╲
            Q_R    Q_L    Q_G
             │      │      │
             ↓      ↓      ↓
             R ←─── L ───→ G
              ╲     │     ╱
               ╲    ↓    ╱
                ─→