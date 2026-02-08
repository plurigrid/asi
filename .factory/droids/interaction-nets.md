---
name: interaction-nets
description: Lafont's interaction nets for optimal parallel λ-reduction. Graph rewriting
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Interaction Nets Skill

> *"The only model where parallelism is not an optimization but the semantics itself."*

## Core Concept

Interaction nets are a graphical model of computation where:
- **Nodes** (agents) have typed ports
- **Wires** connect ports
- **Reduction** happens when two **principal ports** meet
- **No global control** — all reductions are local and can happen in parallel

```
     ┌─●─┐              ┌───┐
  ───┤   ├───    →   ───┤   ├───
     └─●─┘              └───┘
  principal ports      result
     meet
```

## Why It's Strange

1. **No evaluation order** — unlike λ-calculus, no choice between CBV/CBN
2. **Optimal sharing** — work is never duplicated (Lamping's algorithm)
3. **Massively parallel** — every independent redex reduces simultaneously
4. **Linear by default** — resources used exactly once (linear logic connection)

## Interaction Combinators

Lafont's universal basis (3 agents):

```
    ε (eraser)     δ (duplicator)     γ (constructor)
        │              /│\                 /│\
        ●             ● │ ●               ● │ ●
                        │                   │
                        ●                   ●
```

### Reduction Rules

```
γ ─● ●─ γ  →  cross-wire (annihilation)
δ ─● ●─ δ  →  cross-wire (annihilation)  
γ ─● ●─ δ  →  duplication (commutation)
ε ─● ●─ γ  →  erase both aux ports
ε ─● ●─ δ  →  erase both aux ports
```

## HVM / Bend Implementation

[Bend](https://bend-lang.org) compiles to HVM (Higher-order Virtual Machine):

```python
# Bend syntax (Python-like, compiles to interaction nets)
def sum(n):
  if n == 0:
    return 0
  else:
    return n + sum(n - 1)

# Automatically parallelizes via interaction net reduction
# No explicit parallelism needed!
```

### Install & Run

```bash
# Install Bend
cargo install hvm
cargo install bend-lang

# Run with parallelism
bend run program.bend -p 8  # 8 threads
```

## λ-Calculus Encoding

### Abstraction (λx.M)
```
        │ (bound var)
    ┌───●───┐
    │   λ   │
