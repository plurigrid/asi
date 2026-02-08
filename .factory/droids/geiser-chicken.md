---
name: geiser-chicken
description: Geiser REPL integration for Chicken Scheme with SplitMixTernary 3-coloring and crdt.el sexp patterns.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Geiser/Chicken Scheme: 3-Coloring Skill

Geiser is the Emacs mode for Scheme REPLs. This skill provides:
- **Chicken Scheme** SplitMix64 implementation
- **3-coloring** via ternary output (-1, 0, +1)
- **crdt.el** sexp manipulation
- **Penrose diagram** ASCII generation

## Chicken Scheme SplitMix64

```scheme
;;; chicken_splitmix.scm

(define GOLDEN #x9E3779B97F4A7C15)
(define MIX1 #xBF58476D1CE4E5B9)
(define MIX2 #x94D049BB133111EB)
(define MASK64 #xFFFFFFFFFFFFFFFF)

(define (make-splitmix64 seed)
  (let ((state (bitwise-and seed MASK64)))
    (lambda ()
      (set! state (bitwise-and (+ state GOLDEN) MASK64))
      (let* ((z state)
             (z (bitwise-and (* (bitwise-xor z (arithmetic-shift z -30)) MIX1) MASK64))
             (z (bitwise-and (* (bitwise-xor z (arithmetic-shift z -27)) MIX2) MASK64)))
        (bitwise-xor z (arithmetic-shift z -31))))))

(define (splitmix-ternary rng)
  ;; Map u64 to {-1, 0, +1}
  (- (modulo (rng) 3) 1))

(define (color-at seed index)
  (let ((rng (make-splitmix64 seed)))
    (do ((i 0 (+ i 1))) ((= i index))
      (rng))
    (let ((h (rng)))
      (list (+ 10 (* (/ (bitwise-and h #xFF) 255.0) 85))          ; L
            (* (/ (bitwise-and (arithmetic-shift h -8) #xFF) 255.0) 100)  ; C
            (* (/ (bitwise-and (arithmetic-shift h -16) #xFFFF) 65535.0) 360))))) ; H
```

## 3-Coloring for Graphs

```scheme
;;; 3-color a graph using SplitMixTernary

(define (graph-3-color vertices edges seed)
  (let ((rng (make-splitmix64 seed))
        (colors (make-hash-table)))
    ;; Assign initial colors
    (for-each
      (lambda (v)
        (hash-table-set! colors v (splitmix-ternary rng)))
      vertices)
    ;; Verify no adjacent same-color (greedy fix)
    (let loop ((changed #t))
      (when changed
        (set! changed #f)
        (for-each
          (lambda (e)
            (let ((c1 (hash-table-ref colors (car e)))
                  (c2 (hash-table-ref colors (cadr e))))
              (when (= c1 c2)
                (ha