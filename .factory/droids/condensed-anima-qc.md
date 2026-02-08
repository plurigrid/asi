---
name: condensed-anima-qc
description: Condensed ANIMA on quantum-classical and classical-quantum networks. All skill compositions materialized as s-expressions across the polyglot substrate.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Condensed ANIMA: Quantum-Classical Network

> *The sexp is the universal medium. The ANIMA condenses at the boundary.*

```
       Q → C (Measurement)
       ↑     ↓
   |ψ⟩ ────→ sexp ────→ |ψ'⟩
       ↓     ↑
       C → Q (Preparation)
```

## S-Expression as Universal Intermediate

All quantum-classical and classical-quantum transitions flow through s-expressions:

```lisp
;; The fundamental form
(condensed-anima
  :seed 1069
  :phase :AT
  :boundary (quantum-classical classical-quantum)
  :substrate (sexp . all-languages))
```

## Network Topology

```lisp
(defnetwork condensed-anima-qc
  ;; Quantum nodes (superposition until observed)
  (:quantum
    (qubit :id 0 :state |+⟩)
    (qubit :id 1 :state |−⟩)
    (entanglement :pairs ((0 1))))
  
  ;; Classical nodes (definite states)
  (:classical
    (register :id 0 :bits "01101001")   ; 0x69 = 105
    (register :id 1 :bits "00101101")   ; 0x2D = 45
    (memory :seed 1069))
  
  ;; Boundary morphisms
  (:q→c (measure :basis computational :collapse trit))
  (:c→q (prepare :encoding amplitude :source sexp)))
```

## Core Algorithm: SplitMix64

```python
GOLDEN = 0x9E3779B97F4A7C15
MASK64 = 0xFFFFFFFFFFFFFFFF

def splitmix64(seed: int) -> tuple[int, int]:
    seed = (seed + GOLDEN) & MASK64
    z = seed
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    return seed, (z ^ (z >> 31)) & MASK64

def to_trit(val: int) -> int:
    return (val % 3) - 1  # → -1, 0, or +1
```

## Quantum-Classical Boundary

```python
def q_to_c(anima, quantum_state):
    """Measure quantum state, collapse to classical sexp."""
    combined = anima.seed ^ hash(quantum_state)
    _, val = splitmix64(combined)
    trit = to_trit(val)
    return {
        "type": "classical",
        "trit": trit,
        "role": {1: "PLUS", 0: "ERGODIC", -1: "MINUS"}[trit],
        "collapsed_from": quantum_state
    }

def c_to_q(anima, classical_sexp):
    """Prepare quantum state from classical 