---
name: elisp
description: Emacs Lisp reference (106K lines info).
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# elisp

Emacs Lisp reference (106K lines info).

## Basics

```elisp
(defun greet (name)
  "Greet NAME."
  (message "Hello, %s!" name))

(let ((x 1) (y 2))
  (+ x y))
```

## Macros

```elisp
(defmacro when-let ((var expr) &rest body)
  `(let ((,var ,expr))
     (when ,var ,@body)))
```

## Hooks

```elisp
(add-hook 'after-init-hook #'my-setup)
(remove-hook 'before-save-hook #'delete-trailing-whitespace)
```

## Advice

```elisp
(advice-add 'find-file :before #'my-before-find-file)
(advice-add 'save-buffer :after #'my-after-save)
```

## Info

```
C-h i m elisp RET
C-h f <function>
C-h v <variable>
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
