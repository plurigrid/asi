---
name: guile
description: GNU Scheme interpreter (67K lines info).
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# guile

GNU Scheme interpreter (67K lines info).

```bash
guile [options] [script [args]]

-L <dir>    Add load path
-l <file>   Load source
-e <func>   Apply function
-c <expr>   Evaluate expression
-s <script> Execute script
```

## REPL

```scheme
(define (factorial n)
  (if (<= n 1) 1 (* n (factorial (- n 1)))))

(use-modules (ice-9 match))
(match '(1 2 3) ((a b c) (+ a b c)))
```

## Modules

```scheme
(use-modules (srfi srfi-1))   ; List library
(use-modules (ice-9 receive)) ; Multiple values
(use-modules (ice-9 format))  ; Formatted output
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
