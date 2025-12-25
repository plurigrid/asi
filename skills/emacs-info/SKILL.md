---
name: emacs-info
description: "Emacs Info documentation system. Navigate and query Info manuals for Emacs, Elisp, and GNU tools."
metadata:
  trit: 0
  version: "1.0.0"
  bundle: documentation
geodesic: true
moebius: "μ(n) ≠ 0"
---

# Emacs Info Skill

**Trit**: 0 (ERGODIC - documentation mediates between learning and doing)  
**Foundation**: GNU Info + Emacs integration  

## Core Concept

Info is the hypertext documentation format for GNU:
- Structured nodes and menus
- Cross-references between manuals
- Index-based search

## Emacs Commands

```elisp
;; Open Info browser
M-x info

;; Go to specific manual
(info "elisp")
(info "emacs")
(info "org")

;; Search index
M-x info-apropos RET <query> RET

;; Navigate
n - next node
p - previous node
u - up
l - back (history)
```

## Standalone Info

```bash
# Read manual
info emacs
info elisp

# Search
info --apropos=regexp
```

## GF(3) Integration

```elisp
(defun gay-info-trit (node)
  "Return trit based on Info node type."
  (cond
   ((string-prefix-p "Function" node) -1)  ; MINUS: constraint
   ((string-prefix-p "Variable" node) 0)   ; ERGODIC: state
   ((string-prefix-p "Command" node) 1)))  ; PLUS: action
```

## Canonical Triads

```
proofgeneral-narya (-1) ⊗ emacs-info (0) ⊗ xenodium-elisp (+1) = 0 ✓
slime-lisp (-1) ⊗ emacs-info (0) ⊗ geiser-chicken (+1) = 0 ✓
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
