---
name: org
description: Org-mode manual (25K lines info).
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# org

Org-mode manual (25K lines info).

## Structure

```org
* Heading 1
** Heading 2
*** TODO Task [#A]
    DEADLINE: <2025-12-25>
    :PROPERTIES:
    :CUSTOM_ID: task-1
    :END:
```

## Markup

```org
*bold* /italic/ _underline_ =verbatim= ~code~
[[https://example.com][Link]]
#+BEGIN_SRC python
print("hello")
#+END_SRC
```

## Keys

```
TAB       Cycle visibility
C-c C-t   Toggle TODO
C-c C-s   Schedule
C-c C-d   Deadline
C-c C-c   Execute/toggle
C-c '     Edit src block
```

## Export

```elisp
(org-export-dispatch)  ; C-c C-e
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
