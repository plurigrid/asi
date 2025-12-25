---
name: cider-embedding
description: Semantic embeddings for Clojure code navigation via CIDER
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# Cider Embedding Skill

**Status**: Stub
**Trit**: 0 (ERGODIC - embedding space navigation)

## Overview

Semantic embeddings for Clojure code navigation via CIDER.

## Features

- Code similarity search via embeddings
- Semantic code completion
- Cross-reference navigation

## Integration

Extends `cider-clojure` with vector space operations.

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
