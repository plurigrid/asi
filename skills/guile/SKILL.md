---
name: guile
description: GNU Scheme interpreter (67K lines info).
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
