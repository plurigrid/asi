---
name: elisp
description: Emacs Lisp reference (106K lines info).
version: 1.0.0
metadata:
  trit: 0
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



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

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
