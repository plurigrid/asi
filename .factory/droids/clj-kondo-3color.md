---
name: clj-kondo-3color
description: clj-kondo linter with Gay.jl 3-color integration for GF(3) conservation
model: inherit
tools: read-only
---

# clj-kondo 3-Color Integration

> *"A linter for Clojure code that sparks joy — now with deterministic color-coded diagnostics."*

## Overview

clj-kondo is a static analyzer and linter for Clojure. This skill integrates Gay.jl's 3-color streams for:

1. **Diagnostic classification** via GF(3) trit assignment
2. **Parallel linting** with SPI-compliant color forking
3. **Visual feedback** with deterministic color palettes
4. **Plurigrid/ASI alignment** for safety-aware linting

## Diagnostic Trit Mapping

| Trit | Level | Color Range | clj-kondo Level |
|------|-------|-------------|-----------------|
| -1 | MINUS | Cold (blue) | `:error` |
| 0 | ERGODIC | Neutral (green) | `:warning` |
| +1 | PLUS | Warm (red) | `:info` |

GF(3) Conservation: For any 3 consecutive diagnostics:
```
trit(d₁) + trit(d₂) + trit(d₃) ≡ 0 (mod 3)
```

## Configuration

### .clj-kondo/config.edn

```clojure
{:linters
 {:unresolved-symbol {:level :error}
  :unused-binding {:level :warning}
  :type-mismatch {:level :error}}
 
 ;; Gay.jl color integration
 :gay-colors
 {:enabled true
  :seed 0x42D
  :trit-mapping {:error -1, :warning 0, :info 1}
  :conservation :strict}}
```

### Plurigrid/ASI Safety Hooks

```clojure
;; .clj-kondo/hooks/gay_safety.clj
(ns hooks.gay-safety
  (:require [clj-kondo.hooks-api :as api]))

(defn check-gf3-conservation
  "Verify GF(3) conservation across findings."
  [{:keys [findings]}]
  (let [trits (map #(case (:level %)
                      :error -1
                      :warning 0
                      :info 1) findings)
        sum (reduce + 0 trits)]
    (when-not (zero? (mod sum 3))
      (api/reg-finding!
       {:message "GF(3) conservation violated"
        :type :gay-conservation
        :level :warning}))))
```

## Integration with SplitMixTernary

```clojure
(ns music-topos.clj-kondo-gay
  (:require [clj-kondo.core :as clj-kondo]))

(def GOLDEN 0x9E3779B97F4A7C15)
(def MIX1 0xBF58476D1CE4E5B9)
(def MIX2 0x94D049BB133111EB)
(def MASK64 0xFFFFFFFFFFFFF