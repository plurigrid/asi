---
name: borkdude
description: Babashka and ClojureScript runtime selection guidance by @borkdude
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

<!-- Propagated to amp | Trit: 0 | Source: .ruler/skills/borkdude -->

# Borkdude Skill: ClojureScript Runtime Selection

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - runtime neutral)
**Principle**: Right tool for context
**Author**: Michiel Borkent (@borkdude)

---

## Overview

**Borkdude** provides guidance for selecting the appropriate ClojureScript runtime based on execution context. Named after Michiel Borkent, creator of Babashka, SCI, Cherry, Squint, and other Clojure tools.

## Runtime Matrix

| Runtime | Context | JVM | Node | Browser | REPL |
|---------|---------|-----|------|---------|------|
| **Babashka** | Scripting | ✗ | ✗ | ✗ | ✓ |
| **SCI** | Embedded | ✓ | ✓ | ✓ | ✓ |
| **Cherry** | Compiler | ✗ | ✓ | ✓ | ✓ |
| **Squint** | Compiler | ✗ | ✓ | ✓ | ✓ |
| **Scittle** | Browser | ✗ | ✗ | ✓ | ✓ |
| **nbb** | Node | ✗ | ✓ | ✗ | ✓ |

## Decision Tree

```
Start
  │
  ├── Need fast startup? ─────────► Babashka (bb)
  │
  ├── Browser target?
  │     ├── Minimal bundle? ──────► Squint
  │     ├── Full ClojureScript? ──► Cherry  
  │     └── Script tag? ──────────► Scittle
  │
  ├── Node scripting? ────────────► nbb
  │
  └── Embedded interpreter? ──────► SCI
```

## Commands

```bash
# Babashka (scripting)
bb script.clj

# nbb (Node)
npx nbb script.cljs

# Squint (compile to JS)
npx squint compile src/main.cljs

# Cherry (compile with macros)
npx cherry compile src/main.cljs

# Scittle (browser)
# <script src="https://cdn.jsdelivr.net/npm/scittle@0.6.15/dist/scittle.js"></script>
```

## SCI (Small Clojure Interpreter)

Embedded interpreter for sandboxed evaluation:

```clojure
(require '[sci.core :as sci])

(def ctx (sci/init {:namespaces {'user {'foo (fn [] "bar")}}}))

(sci/eval-string* ctx "(user/foo)")
;; => "bar"
```

## Cherry vs Squint

| Feature | Cherry | Squint |
|---------|--------|--------|
| ClojureScript compat | High | Medium |
| Bundle size | Larger | Smaller |
| Macros | Full support | Limited |
| Interop | CLJS-style | JS-native 