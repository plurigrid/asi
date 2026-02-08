---
name: homoiconic-rewriting
description: Unified homoiconic graph rewriting - λ-calculus, interaction nets, ACSets, CUDA parallelism
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Homoiconic Rewriting

> *Code = Data = Graph = Parallel Reduction*

**Trit**: 0 (ERGODIC - coordinates the stack)

## Core Synthesis

```
┌─────────────────────────────────────────────────────────────────┐
│              HOMOICONIC REWRITING PIPELINE                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   λ-term ──quote──→ S-exp ──parse──→ INet ──CUDA──→ Result     │
│     │                  │               │              │         │
│   typed              data            graph         parallel     │
│   code            (homoiconic)     rewriting      reduction     │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## GF(3) Balanced Dependencies

| Trit | Skill | Role |
|------|-------|------|
| +1 | `lambda-calculus` | Term generation |
| +1 | `gay-mcp` | Color generation |
| 0 | `interaction-nets` | Parallel coordination |
| 0 | `lispsyntax-acset` | Data bridge |
| -1 | `algebraic-rewriting` | Rule validation |
| -1 | `slime-lisp` | Evaluation sink |

**Sum**: (+1+1) + (0+0) + (-1-1) = 0 ✓

## The Homoiconic Property

### Level 1: S-expressions (Lisp)

```clojure
;; Code
(+ 1 2)

;; Data (same representation!)
'(+ 1 2)

;; Transform code as data
(map inc '(+ 1 2))  ; → (1 2 3)
```

### Level 2: Interaction Nets (Graphs)

```
Code (λ-term):     Data (graph):         Rewrite (reduction):
  λx. x x          ┌───┐                 ┌───┐     ┌───┐
                   │ λ │──┬──┐           │ @ │─────│ @ │
                   └─┬─┘  │  │           └─┬─┘     └─┬─┘
                     │    │  │             │         │
                   ┌─┴─┐  │  │     →       └────┬────┘
                   │ @ │──┘  │                  │
                   └─┬─┘     │               result
                     └───────┘
```

### Level 3: ACSets (Algebraic Databases)

```julia
# Code: rewrite r