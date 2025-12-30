---
name: scheme
description: GNU Scheme ecosystem = guile + goblins + hoot + fibers.
metadata:
  trit: 0
---

# scheme

GNU Scheme ecosystem = guile + goblins + hoot + fibers.

## Atomic Skills

| Skill | Lines | Domain |
|-------|-------|--------|
| guile | 67K | Interpreter |
| goblins | 6.5K | Distributed objects |
| hoot | 4K | WebAssembly |
| fibers | 2K | Concurrent ML |
| r5rs | 1K | Standard |

## Compose

```scheme
;; guile + goblins + hoot
(use-modules (goblins)
             (goblins actor-lib methods)
             (hoot compile))

(define-actor (counter bcom count)
  (methods
    ((get) count)
    ((inc) (bcom (counter bcom (+ count 1))))))
```

## Wasm Pipeline

```bash
guile -c '(compile-to-wasm "app.scm")'
```

## FloxHub

```bash
flox pull bmorphism/effective-topos
flox activate -d ~/.topos
```



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Cheminformatics
- **rdkit** [○] via bicomodule
  - Hub for chemistry

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
