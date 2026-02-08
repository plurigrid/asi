---
name: planar-isotopy-screen
description: Planar Isotopy Screen Mapping
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Planar Isotopy Screen Mapping

Maps thread states and observations to screen positions using planar isotopy principles.

## Trit Value
**0 (ERGODIC)** - Coordinate between spatial regions

## Purpose
Transform abstract thread relationships into concrete screen positions while preserving topological invariants:
- **Adjacency**: Neighboring trits occupy adjacent screen regions
- **Handedness**: MINUS→left, ERGODIC→center, PLUS→right
- **Conservation**: Screen area sum is invariant under isotopy

## Screen Region Mapping

```
┌─────────────────┬─────────────────┬─────────────────┐
│                 │                 │                 │
│     MINUS       │    ERGODIC      │     PLUS        │
│    (left)       │    (center)     │    (right)      │
│                 │                 │                 │
│  Cold hues      │  Neutral hues   │  Warm hues      │
│  180-300°       │  60-180°        │  0-60°,300-360° │
│                 │                 │                 │
│  Validator      │  Coordinator    │  Generator      │
│                 │                 │                 │
└─────────────────┴─────────────────┴─────────────────┘
```

## Position Computation

```clojure
(defn seed->screen-position [seed trit screen-width screen-height]
  "Map seed deterministically to (x, y) within trit's region.

   Uses SplitMix64 decomposition:
   - High bits → x offset
   - Low bits → y offset"
  (let [region (trit->region trit screen-width)
        [rand1 seed'] (splitmix64 seed)
        [rand2 _] (splitmix64 seed')
        x (+ (:x region) (* (:width region) (/ rand1 MASK64)))
        y (* screen-height (/ rand2 MASK64))]
    {:x x :y y :region trit}))
```

## Observation Lines

When thread A observes thread B, draw a line between their screen positions:

```clojure
(defn observation-line [observer observed]
  {:from (seed->screen-position (:seed observer) (:trit observer))
   :to (seed->screen-position (:seed observed) (:trit observed))
   :gf3-sum (mod (+ (:trit observer) (:t