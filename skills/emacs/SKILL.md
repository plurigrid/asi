---
name: emacs
description: Emacs ecosystem = elisp + org + gnus + tramp + eglot.
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# emacs

Emacs ecosystem = elisp + org + gnus + tramp + eglot.

## Atomic Skills

| Skill | Lines | Domain |
|-------|-------|--------|
| elisp | 106K | Programming |
| org | 25K | Documents |
| gnus | 15K | Mail/News |
| tramp | 8K | Remote files |
| eglot | 2K | LSP |
| transient | 3K | Menus |

## Info Access

```
C-h i           Info browser
C-h i m elisp   Elisp manual
C-h i m org     Org manual
C-h f           Describe function
C-h v           Describe variable
```

## Init

```elisp
(use-package org
  :config
  (setq org-directory "~/org"))

(use-package eglot
  :hook ((python-mode . eglot-ensure)))
```

## FloxHub

```bash
flox pull bmorphism/effective-topos
emacs --with-profile topos
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
