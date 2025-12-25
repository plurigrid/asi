---
name: scheme
description: GNU Scheme ecosystem = guile + goblins + hoot + fibers.
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
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

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
