---
name: hoot
description: Scheme→WebAssembly compiler (4K lines info).
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# hoot

Scheme→WebAssembly compiler (4K lines info).

## Compile

```bash
guild compile-wasm -o out.wasm script.scm
```

## Features

- Full tail call optimization
- First-class continuations
- JavaScript interop
- Standalone Wasm modules

## Example

```scheme
(define-module (my-module)
  #:export (greet))

(define (greet name)
  (string-append "Hello, " name "!"))
```

## Runtime

```javascript
import { Hoot } from '@aspect/guile-hoot';
const mod = await Hoot.load('out.wasm');
mod.greet("World");
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
