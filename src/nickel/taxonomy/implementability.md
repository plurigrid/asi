# Aperiodic Algorithm Implementability Assessment

## Summary Matrix

| # | Algorithm Class | Status | Existing Code | Effort |
|---|----------------|--------|---------------|--------|
| 1 | **Substitution** | IMPLEMENTED | `aperiodic_monotile.clj` | Done |
| 2 | **Combinatorial Coords** | IMPLEMENTED | `triad_spectre_unified.clj` | Done |
| 3 | **Projection** | NOT IMPLEMENTED | — | Medium |
| 4 | **Matching Rules** | NOT IMPLEMENTED | — | High |
| 5 | **Random Walk** | IMPLEMENTED | 3 files | Done |
| 6 | **Transducers** | NOT IMPLEMENTED | — | Medium |
| 7 | **BFS Generation** | IMPLEMENTED | `aperiodic_monotile.clj` | Done |

---

## Class 1: Substitution — IMPLEMENTED

**Location:** `aperiodic_monotile.clj:72-81`

```clojure
(def super-rules
  {:G [:P :D nil :Theta :S :X :Phi :G]
   :D [:X :D :X :Phi :S :P :Phi :G]
   :J [:Psi :D :P :Phi :S :P :Phi :G]
   ...})
```

**What's working:**
- Spectre 9-hexagon substitution system
- Metatile expansion rules
- 14-vertex Spectre polygon geometry

**Missing:**
- Penrose P2/P3 Robinson triangle subdivision
- Hat metatile system (H, T, P, F)

---

## Class 2: Combinatorial Coordinates — IMPLEMENTED

**Location:** `triad_spectre_unified.clj:47-144`

```clojure
(defrecord TriadCoords [index coords trit-sum batch-color])

(defn extend-triad-coords [tc depth rng]
  "Extend coordinates lazily to reach specified depth.")

(defn step-to-neighbor [tc edge rng locality-threshold]
  "Step to neighboring triad via edge.")
```

**Also:** `aperiodic_monotile.clj:60-199`
```clojure
(defrecord SpectreCoords [index coords hex-colour prev-hex-colour incoming-edge])
(defn extend-coords-lazily [coords n rng] ...)
(defn step-to-neighbor [coords edge rng] ...)
```

**What's working:**
- Tatham-style lazy coordinate extension
- Edge-based neighbor navigation
- Hierarchical batch/triad nesting

---

## Class 3: Projection (de Bruijn) — NOT IMPLEMENTED

**Required components:**
1. n-dimensional lattice generation
2. Irrational shift vector handling
3. Projection matrix (R^n → R^2)
4. Grid intersection computation
5. Dual graph construction

**Implementation sketch:**
```clojure
(defn pentagrid [n gamma]
  "Generate n families of parallel lines with shift gamma"
  (for [k (range n)
        j (range -max-j max-j)]
    {:family k
     :offset (+ j (nth gamma k))
     :angle (* k (/ Math/PI n))}))

(defn project-5d-to-2d [point]
  "Project 5D lattice point to 2D plane"
  (let [basis (for [k (range 5)]
                [(Math/cos (* 2 Math/PI k 1/5))
                 (Math/sin (* 2 Math/PI k 1/5))])]
    (reduce (fn [[x y] [bx by p]]
              [(+ x (* p bx)) (+ y (* p by))])
            [0 0]
            (map conj basis point))))
```

**Effort:** Medium (2-3 hours)
**Limitation:** Only produces rhombus tilings (Penrose), not Hat/Spectre

---

## Class 4: Matching Rules — NOT IMPLEMENTED

**Required components:**
1. Edge decoration system
2. Vertex configuration enumeration
3. Constraint propagation engine OR SAT solver integration
4. Backtracking search

**Options:**
- **Option A:** Pure Clojure constraint propagation
- **Option B:** Shell out to MiniSat/Z3
- **Option C:** Use `core.logic` (miniKanren)

**Implementation sketch:**
```clojure
(def penrose-edge-rules
  "Arrow decorations on Penrose tiles"
  {:thick-rhomb {:edge-0 :arrow-in :edge-1 :arrow-out ...}
   :thin-rhomb  {:edge-0 :arrow-out :edge-1 :arrow-in ...}})

(defn valid-vertex? [tiles-around-vertex]
  "Check if vertex configuration is one of 7 legal types"
  (contains? legal-vertex-types (vertex-signature tiles-around-vertex)))

(defn propagate-constraints [partial-tiling]
  "Wave function collapse style propagation"
  ...)
```

**Effort:** High (1-2 days)
**Complexity:** SAT encoding is non-trivial

---

## Class 5: Random Walk — IMPLEMENTED

**Location 1:** `triad_metatile.clj:132-170`
```clojure
(defn random-walk-with-replacement [triads adjacency rng steps start-id] ...)
(defn random-walk-without-replacement [triads adjacency rng max-steps start-id] ...)
```

**Location 2:** `triad_spectre_unified.clj:150-189`
```clojure
(defn random-walk-spectre-style [start-tc num-steps rng locality with-replacement?]
  "with-replacement? = true  → can revisit (periodic potential)
   with-replacement? = false → no revisits (aperiodic)")
```

**Location 3:** `aperiodic_monotile.clj:137-163`
```clojure
(defn walk-step [x y angle length] ...)
(defn complete-walk [positions step-length start-x start-y] ...)
```

**Angle derivation methods implemented:**
- `(x * y) mod 360` — Ben-Edwards44 style
- `(idx+1) * (batch_sum+1) * (triad_sum+1) * 17 mod 360` — Hierarchical

---

## Class 6: Transducers — NOT IMPLEMENTED

**Required components:**
1. State machine definition
2. Transition tables per tile type × edge
3. Coordinate string parser
4. Output string builder

**Implementation sketch:**
```clojure
(def p2-transducer-states
  "States for P2 Penrose neighbor lookup"
  {:start {:A {:edge-0 [:emit-B :state-1]
               :edge-1 [:emit-U :state-2]
               :edge-2 [:carry :state-3]}
           :B {...}
           :U {...}
           :V {...}}
   :state-1 {...}
   ...})

(defn run-transducer [coord-string edge]
  "Transform coordinate string to neighbor's coordinates"
  (loop [state :start
         input (reverse coord-string)
         output []]
    (if (empty? input)
      (reverse output)
      (let [[emit next-state] (get-in transducer-states [state (first input) edge])]
        (recur next-state (rest input) (conj output emit))))))
```

**Effort:** Medium (3-4 hours)
**Benefit:** O(n) neighbor lookup where n = coordinate depth

---

## Class 7: BFS Generation — IMPLEMENTED

**Location:** `aperiodic_monotile.clj:205-229`

```clojure
(defn generate-patch [start-coords bounds rng]
  "Generate patch of Spectres via BFS, staying within bounds"
  (loop [queue [(spectre-coords-new)]
         visited #{}
         tiles []]
    (if (empty? queue)
      tiles
      (let [current (first queue)
            ...]
        (recur (concat (rest queue)
                      (map #(assoc current :coords %) neighbors))
               (conj visited coord-key)
               (conj tiles {:coords current :pos pos}))))))
```

**What's working:**
- BFS flood-fill from seed
- Bounds checking
- Visited set for deduplication
- Neighbor enumeration via 14 edges

---

## Recommended Next Steps

### Immediate (can implement now):

1. **Penrose Subdivision** — Add Robinson triangle rules to `aperiodic_monotile.clj`
2. **Transducers** — Create `aperiodic_transducers.clj` with state machine lookup

### Medium-term:

3. **Projection** — Create `debruijn_multigrid.clj` for Penrose-only projection
4. **Hat Metatiles** — Add H/T/P/F expansion rules

### Long-term:

5. **Matching Rules** — Integrate SAT solver or implement constraint propagation

---

## File Inventory

| File | Classes Implemented | Lines |
|------|---------------------|-------|
| `aperiodic_monotile.clj` | 1, 2, 5, 7 | 355 |
| `triad_spectre_unified.clj` | 2, 5 | 392 |
| `triad_metatile.clj` | 5 | ~200 |
| `aperiodic_algorithm_taxonomy.clj` | (docs only) | 550 |
