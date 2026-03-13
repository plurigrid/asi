---
name: asi-scsh-pipeline
description: "scsh-style Scheme pipeline patterns for per-letter world operations. Process forms, pipes, and redirections as pure Guile data transforms — no /bin/sh required."
trit: 1
version: 1.0.0
seed: 1069
triad: "gf3-conservation-oracle (-1) ⊗ gf3-tripartite (0) ⊗ asi-scsh-pipeline (+1) = 0"
---

# ASI scsh Pipeline

> scsh = Scheme Shell. Everything is a port, process, or file descriptor.
> But under flox activate, popen has fd inheritance issues.
> So: pure data transforms piped through Guile port I/O.

## Role: PLUS (+1) — Generate Pipeline Outputs

### The scsh Idiom in Practice

```scheme
;; scsh way: records as process groups, transforms as pipes, ports as redirections
(define-record-type <cap>
  (make-cap op args trit)
  cap?
  (op   cap-op)
  (args cap-args)
  (trit cap-trit))

;; "pipe": cap → string (SBPL rule)
(define (cap->sbpl cap) ...)

;; "redirect": profile → file port
(define (write-profile! dir prof) ...)

;; "pipeline": caps → profile-string → file
(for-each (lambda (p) (write-profile! dir p)) profiles)
```

### Why Not Actual scsh?

scsh (Scheme Shell by Olin Shivers) uses `run`, `exec-epf`, `|`, `&&` process forms.
These require `fork/exec` and `/bin/sh`. Under flox activate on macOS:
- `open-input-pipe` fails with "Bad file descriptor" (fd inheritance blocked)
- `system*` works but loses Scheme's composability

The solution: keep scsh's philosophy (everything is a transform) but implement
with pure Guile port I/O instead of Unix process primitives.

### Proven Working

`~/worlds/seatbelt-scsh.scm` generates 33 profiles in pure Guile:
```bash
cd ~/worlds/z && flox activate -- guile -s ~/worlds/seatbelt-scsh.scm /tmp/sb
```
All profiles pass `sandbox-exec` testing. No shell involved.

### Composing with Other Skills

| Source Skill | scsh Pattern |
|---|---|
| sdr-borges-reafference | `.scm` files use `(use-modules (goblins))` — same pattern |
| goblins-adapter.scm | 500+ lines of pure Guile, no shell |
| self_indexing_automata.scm | Quine property: code describes itself |
| gf3-kanren.scm | miniKanren relations — pure logic |

All Goblins skills already follow scsh philosophy: no shell, just Scheme.
