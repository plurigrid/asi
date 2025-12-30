---
name: goblins
description: Distributed object capability system (6.5K lines info).
metadata:
  trit: 0
---

# goblins

Distributed object capability system (6.5K lines info).

## Model

```
peer → vat → actormap → {refr: behavior}
```

## Operators

```scheme
($  obj method args...)   ; Sync (near only)
(<- obj method args...)   ; Async (near/far)
```

## Vat

```scheme
(define vat (spawn-vat))
(define greeter
  (vat-spawn vat
    (lambda (bcom)
      (lambda (name)
        (format #f "Hello, ~a!" name)))))

($ greeter "World")  ; => "Hello, World!"
```

## OCapN

Object Capability Network for secure p2p via CapTP.



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
