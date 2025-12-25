---
name: goblins
description: Distributed object capability system (6.5K lines info).
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
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
