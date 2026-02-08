---
name: dynamic-sufficiency-goblin
description: Self-regulating Goblins actor implementing Ivan Illich's dynamic sufficiency
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Dynamic Sufficiency Goblin

**Real Spritely Goblins** actor that self-regulates workforce via load-based spawning. GF(3) conserved.

## Illich's Principle

> "Tools that demand only threshold skill, foster autonomy."

A goblin that:
1. Monitors load (free energy)
2. Spawns helpers when overwhelmed (>80%)
3. Releases helpers when idle (<30%)
4. Maintains `Σ trits ≡ 0 (mod 3)`

## Real Guile Goblins Implementation

```scheme
(use-modules (goblins)
             (goblins actor-lib methods)
             (ice-9 format)
             (srfi srfi-1))

(define (^sufficiency-goblin bcom capacity)
  (define queue '())
  (define helpers '())
  (define my-trit 0)

  (define (load-factor)
    (/ (length queue) (max 1 capacity)))

  (define (gf3-sum)
    (+ my-trit (fold + 0 (map cdr helpers))))

  (define (balanced-trit-for-spawn)
    (case (modulo (+ (gf3-sum) 300) 3)
      ((0) 0) ((1) -1) ((2) 1)))

  (methods
   ((enqueue item)
    (set! queue (cons item queue))
    (when (> (load-factor) 0.8)
      (let* ((helper-trit (balanced-trit-for-spawn))
             (helper (spawn ^sufficiency-goblin 2)))
        (set! helpers (cons (cons helper helper-trit) helpers)))))

   ((release-idle)
    (when (and (< (load-factor) 0.3) (pair? helpers))
      (set! helpers (cdr helpers))))

   ((status)
    `((load . ,(load-factor))
      (helpers . ,(length helpers))
      (gf3 . ,(gf3-sum))
      (conserved? . ,(zero? (modulo (gf3-sum) 3)))))))

;; Usage with actormap (no networking required)
(define am (make-actormap))
(define goblin (actormap-spawn! am ^sufficiency-goblin 3))
(actormap-run! am (lambda () ($ goblin 'enqueue "work")))
```

## Run

```bash
cd ~ && flox activate -- guile -e main /tmp/sufficiency-goblin.scm
```

## Output

```
╔═══════════════════════════════════════════════════════════════╗
║     DYNAMIC SUFFICIENCY GOBLIN (Real Spritely Goblins)        ║
╠═══════════════════════════════════════════════════════════════╣

Created goblin with capacity=3

  Enqueued: 1 items, loa