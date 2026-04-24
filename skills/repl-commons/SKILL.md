---
name: repl-commons
description: "Atlas of REPL-using skills across Clojure, Scheme, Julia, Python, Hy, Unison, Emacs-bridged, and database families. Use when picking an interactive-evaluation tool, threading forms across language boundaries, or establishing a cross-language nREPL/comint/Geiser pipeline."
---

# repl-commons

A single entry point that intermixes every REPL-primary skill in the repo. Edges emitted below make each family member depth-1 from this hub.

## Families

### clojure-repl

`clojure` · `babashka` · `babashka-clj` · `cider-clojure` · `cider-embedding` · `jo-clojure` · `joker-lint` · `joker-sims-parser` · `jank` · `jank-llvm` · `borkdude` · `squint-runtime` · `abductive-repl` · `clj-kondo-3color`

Primary entry: `clojure`. Fastest startup: `babashka`. Editor-embedded: `cider-clojure` → `cider-embedding`. Alternate runtimes: `jank` (LLVM), `jank-llvm`, `squint-runtime` (JS), `jo-clojure` (C).

### scheme-repl

`slime-lisp` · `geiser-chicken` · `guile` · `guile-goblins-hoot` · `little-schemer` · `scheme` · `srfi` · `hoot`

Primary entry: `guile`. Pedagogical: `little-schemer` → `scheme` → `srfi`. WASM target: `hoot` (via `guile-goblins-hoot`). Host-embedded: `slime-lisp` · `geiser-chicken`.

### julia-repl

`sicm` · `sicmutils` · `sicp` · `quarto-julia` · `julia-gay` · `julia-scientific` · `julia-gpu-kernels` · `julia-tempering`

Canonical: `julia-scientific`. Functional/classical mechanics: `sicm` → `sicmutils` ← `sicp`. Reporting: `quarto-julia`. GPU: `julia-gpu-kernels`. Sampler: `julia-tempering`. Color/hash: `julia-gay`.

### python-repl

`jupyter` · `jupyter-notebook` · `python-development` · `pymc` · `monad-bayes-asi-interleave` · `ipa-safety`

Canonical: `jupyter` ↔ `jupyter-notebook`. Dev loop: `python-development`. Bayesian: `pymc` · `monad-bayes-asi-interleave`. Instrumented: `ipa-safety`.

### hy-repl

`hy-emacs` · `hy-regime`

Lisp-on-Python dialect. Pairs with `emacs` via `hy-emacs`; regime notes in `hy-regime`. Often co-loaded with `clojure` via `cider-embedding`.

### unison-repl

`unison` · `unison-acset`

UCM stateful codebase REPL. `unison-acset` = schema-pinned flavor. External bridge: `goblins` / `captp`.

### emacs-bridge

`emacs` · `elisp` · `org-babel-execution` · `alice-emacs-mods` · `bob-emacs-mods` · `xenodium-elisp` · `sexp-neighborhood` · `proofgeneral-narya`

The shared runtime that intermixes every family above via `comint` / `emacsclient` / tramp. Host-level setup: `alice-emacs-mods`. Operational loop: `bob-emacs-mods`. Polyglot literate: `org-babel-execution`. Proof REPL: `proofgeneral-narya`. Structural nav: `sexp-neighborhood`.

### database-repl

`duckdb-guard` · `duckdb-ies` · `ducklake-walk` · `ducklake-semantic-analyzer`

SQL-as-REPL family. Hot loop: `duckdb-guard`. Temporal browsing: `ducklake-walk`. Semantic: `ducklake-semantic-analyzer`.

### specialized

`specter-acset` · `lispsyntax-acset` · `modelica-lispsyntax-interleave`

Specter-style navigation over REPL state: `specter-acset`. Lisp-syntax hosts for other languages: `lispsyntax-acset`, `modelica-lispsyntax-interleave`.

## Cross-family threading

- **Clojure ↔ Scheme:** `guile-goblins-hoot` + `squint-runtime` compile to shared runtime (WASM/JS), tied by `goblins` + `captp`.
- **Clojure ↔ Julia:** `lispsyntax-acset` makes Julia addressable from `clojure` via `cider-embedding`.
- **Clojure ↔ Emacs:** `cider-clojure` → `cider-embedding` → `alice-emacs-mods` / `bob-emacs-mods`.
- **Julia ↔ Python:** `monad-bayes-asi-interleave` crosses via `pymc`'s Bayesian core.
- **Unison ↔ Scheme:** `unison` ↔ `guile-goblins-hoot` via `captp` / OCapN.
- **Any ↔ Emacs:** every family above surfaces in `emacs` / `elisp` via `org-babel-execution`.

## Use when

- Picking an interactive evaluator for a language-agnostic task
- Building a polyglot pipeline (REPL-to-REPL messaging via `captp` or nREPL)
- Onboarding a new contributor: hand them this atlas first
- Planning a skill whose primary tool is "talk to a live runtime"
