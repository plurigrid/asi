---
name: slime-lisp
description: SLIME integration for Common Lisp development
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# SLIME Lisp Skill

**Status**: Stub
**Trit**: -1 (MINUS - contravariant to Clojure's covariant)

## Overview

SLIME integration for Common Lisp development.

## Commands

- `slime` - Start SLIME connection
- `slime-eval-defun` - Evaluate current definition
- `slime-compile-and-load-file` - Compile and load buffer

## Integration

Dual to `cider-clojure` for Common Lisp workflows.

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
