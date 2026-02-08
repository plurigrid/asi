---
name: sdf
description: "Software Design for Flexibility: Sussman & Hanson's additive programming, combinators, propagators, and generic dispatch for evolvable systems"
model: inherit
tools: read-only
---

# SDF Skill: Software Design for Flexibility

> *"It is better to have 100 functions operate on one data structure than 10 functions on 10 data structures."*
> — Alan Perlis (via Sussman & Hanson)

Geometric morphism from the MIT Press 2021 text, preserving the compositional structure as an ACSet with GF(3) coloring for trifurcated processing.

## Overview

**Software Design for Flexibility**  
by Chris Hanson and Gerald Jay Sussman  
MIT Press, 2021  
ISBN: 978-0262045490

The successor to SICP focused on **additive programming**—building systems that can evolve by adding new capabilities without modifying existing code.

## Core Principles

### The Flexibility Mandate

1. **Additive over Modificative**: New features via addition, not mutation
2. **Generic over Specific**: Operations that work across types
3. **Compositional over Monolithic**: Small combinable pieces
4. **Declarative over Imperative**: Constraints over control flow

## Chapters with GF(3) Trit Assignment

### Part I: Flexibility in Primitive Parts [PLUS]

#### Chapter 1: Flexibility through Abstraction (+1)
- Combinators as primitive building blocks
- `compose`, `parallel-combine`, `spread-combine`
- Arity management and currying patterns

Key combinator:
```scheme
(define (compose f g)
  (lambda args
    (f (apply g args))))
```

#### Chapter 2: Domain-Specific Languages (-1)
- Embedded DSLs via combinators
- Wrapper strategies for APIs
- Pattern-directed invocation

### Part II: Flexibility through Dispatch [ERGODIC]

#### Chapter 3: Variations on an Arithmetic Theme (0)
- Generic arithmetic operations
- Type coercion lattices
- Symbolic vs numeric duality

#### Chapter 4: Pattern Matching (+1)
- Unification as composition
- Segment variables and pattern operators
- Match combinators

```scheme
(define (match:element variable)
  (lambda (data dictionary succeed)
    (let ((binding (assq variable dictionary)))
      (if binding
          (and (equal? (cdr binding) data)
               (succeed dic