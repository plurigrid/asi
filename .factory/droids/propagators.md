---
name: propagators
description: Sussman/Radul propagator networks for constraint propagation and bidirectional
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Propagators Skill

> *"The Art of the Propagator" — Radul & Sussman, 2009*

## Core Concept

Propagators are autonomous machines that:
1. **Watch** cells for new information
2. **Compute** derived values
3. **Add** information to other cells
4. Repeat until **fixpoint**

```
  ┌──────┐         ┌──────┐
  │cell A│────────▶│cell B│
  └──────┘  prop   └──────┘
      │                │
      │    ┌──────┐    │
      └───▶│cell C│◀───┘
           └──────┘
```

**No control flow.** Information flows until nothing new can be derived.

## Why It's Strange

1. **Bidirectional** — constraints work both ways
2. **Monotonic** — cells only gain information, never lose it
3. **Mergeable** — conflicting info produces refined info (or contradiction)
4. **Concurrent** — all propagators run "simultaneously"

## Cell Lattice

Cells hold values from a **join-semilattice**:

```
        ⊤ (contradiction)
       /|\
      / | \
     /  |  \
   3.14  e  √2
     \  |  /
      \ | /
       \|/
        ⊥ (nothing)
```

- ⊥ = "I know nothing"
- Value = "I know this specific thing"
- ⊤ = "Contradiction! Conflicting claims"

## Basic Operations

```scheme
;; Create cells
(define-cell a)
(define-cell b)
(define-cell c)

;; Add propagator: c = a + b
(p:+ a b c)

;; Set values (can be in any order!)
(add-content a 3)
(add-content b 4)

;; c automatically becomes 7
(content c)  ; → 7

;; BIDIRECTIONAL: set c, derive a!
(add-content c 10)
(add-content b 4)
(content a)  ; → 6 (inferred!)
```

## Partial Information

```scheme
;; Intervals
(define-cell x)
(add-content x (make-interval 0 10))   ; x ∈ [0, 10]
(add-content x (make-interval 5 15))   ; x ∈ [5, 10] (intersection!)

;; Symbolic
(add-content x 'positive)
(add-content x 7)  ; Consistent: 7 is positive

;; Contradiction
(add-content x 'negative)  ; → ⊤ (7 is not negative!)
```

## Implementation

### Minimal Propagator in Python

```python
class Cell:
    def __init__(self):
        self.content = Nothing()
        self.neighbors = []  # Prop