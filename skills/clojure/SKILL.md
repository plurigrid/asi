---
name: clojure
description: Clojure ecosystem = babashka + clj + lein + shadow-cljs.
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# clojure

Clojure ecosystem = babashka + clj + lein + shadow-cljs.

## Atomic Skills

| Skill | Startup | Domain |
|-------|---------|--------|
| babashka | 10ms | Scripting |
| clj | 2s | JVM REPL |
| lein | 3s | Build tool |
| shadow-cljs | 5s | ClojureScript |

## Quick Start

```bash
# Scripting (fast)
bb -e '(+ 1 2 3)'

# JVM (full)
clj -M -m myapp.core

# Web (ClojureScript)
npx shadow-cljs watch app
```

## deps.edn

```clojure
{:deps {org.clojure/clojure {:mvn/version "1.12.0"}}
 :aliases {:dev {:extra-paths ["dev"]}
           :test {:extra-deps {lambdaisland/kaocha {:mvn/version "1.0"}}}}}
```

## bb.edn

```clojure
{:tasks {:build (shell "clj -T:build uber")
         :test (shell "clj -M:test")
         :repl (clojure "-M:dev -m nrepl.cmdline")}}
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
