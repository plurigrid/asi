---
name: squint-runtime
description: Squint ClojureScript runtime for minimal JS output compilation
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Squint Runtime Skill

**Status**: ✅ Production Ready
**Author**: Michiel Borkent (borkdude)
**Trit**: 0 (ERGODIC - neutral transport)
**Stars**: 1.2k+

---

## Overview

Squint is a **light-weight ClojureScript dialect** that compiles to JavaScript with minimal runtime overhead. It's the "minimal" alternative in borkdude's browser runtime spectrum.

## When to Use Squint vs Cherry

| Aspect | Squint | Cherry 🍒 |
|--------|--------|-----------|
| **Runtime size** | Minimal (~10KB) | Full cljs.core (~100KB) |
| **Semantics** | JS-like | Full CLJS |
| **Data structures** | JS objects/arrays | Persistent immutable |
| **Keywords** | Strings | CLJS keywords |
| **Interop** | Seamless | Requires macros |
| **JSX** | ❌ | ✅ |
| **Use case** | Small scripts, interop | Full applications |

## Installation

```bash
npm install squint-cljs@latest
```

## Usage

```clojure
;; example.cljs
(ns example)

;; Functions compile to regular JS functions
(defn greet [name]
  (str "Hello, " name "!"))

;; JS interop is seamless
(js/console.log (greet "World"))

;; Object destructuring works naturally
(defn process [{:keys [a b c]}]
  (+ a b c))

(process #js {:a 1 :b 2 :c 3})  ; => 6
```

### Compile and Run

```bash
# Compile to JS
npx squint compile example.cljs

# Run directly
npx squint run example.cljs
```

## Key Differences from CLJS

1. **Data structures are JS native**:
   ```clojure
   {:a 1}  ; => {a: 1} in JS (plain object)
   [1 2 3] ; => [1, 2, 3] in JS (array)
   ```

2. **Keywords become strings**:
   ```clojure
   :foo ; => "foo" in JS
   ```

3. **No persistent data structures** (use JS mutation)

4. **Faster interop** (no conversion needed)

## Integration with Gay.jl Colors

```clojure
(ns squint.gay-colors)

;; SplitMix64 constants
(def GOLDEN 0x9E3779B97F4A7C15)
(def MASK64 0xFFFFFFFFFFFFFFFF)

(defn splitmix64 [state]
  (let [s (bit-and (+ state GOLDEN) MASK64)
        z (-> s
              (bit-xor (unsigned-bit-shift-right s 30))
              (* 0xBF58476D1CE