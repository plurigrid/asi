---
name: triangle-sparsifier
description: Triangle inequality for maximally correct world choice sparsification
  via snips.duckdb random walks.
metadata:
  trit: -1
  sources:
  - /Users/bob/ies/paper_extracts/mathpix_snips/snips.duckdb
  - world-hopping skill
  - glass-bead-game skill
  interface_ports:
  - References
  - Commands
  - Integration with
  - Related Skills
---
# Triangle Sparsifier: World Choice via Metric Pruning

Navigate possible worlds by **sparsifying** choices using triangle inequality. Random walk through `snips.duckdb` LaTeX extracts to discover metric structures, then prune world graphs to minimal spanning configurations.

## Core Principle

Given worlds W₁, W₂, W₃, if d(W₁,W₃) > d(W₁,W₂) + d(W₂,W₃), the direct edge W₁→W₃ is **redundant** and can be sparsified away.

```
Triangle Inequality: d(A,C) ≤ d(A,B) + d(B,C)

If violated → direct path is IMPOSSIBLE
If saturated (equality) → geodesic, KEEP
If slack → potential redundancy, PRUNE candidate
```

## Snips Random Walk

### DuckDB Integration

```clojure
#!/usr/bin/env bb
;; triangle_walk.bb - Random walk through snips extracting metric structures

(require '[babashka.process :as p]
         '[cheshire.core :as json])

(def SNIPS-DB "~/ies/paper_extracts/mathpix_snips/snips.duckdb")

(defn random-snips [n seed]
  "Sample n random snips with deterministic seed"
  (let [sql (format "SELECT id, category, latex FROM snips 
                     ORDER BY hash(id || '%d') LIMIT %d" seed n)
        result (p/shell {:out :string} 
                        "duckdb" (str SNIPS-DB) "-json" "-c" sql)]
    (json/parse-string (:out result) true)))

(defn extract-metric-snips [snips]
  "Filter snips containing metric/distance/inequality concepts"
  (filter (fn [{:keys [latex]}]
            (some #(re-find % (or latex ""))
                  [#"(?i)triangle"
                   #"(?i)inequality"
                   #"(?i)metric"
                   #"(?i)distance"
                   #"d\s*\([^)]+,[^)]+\)"  ; d(x,y) pattern
                   #"\\leq.*\+.*\\leq"     ; chain inequality
                   #"geodesic"]))
          snips))
```

### Walk Strategy

```clojure
(def WALK-STRATEGIES
  {:random-uniform
   "Sample uniformly at random"
   
   :category-biased
   "Weight by category (prefer category_theory, math)"
   
   :metric-seeking
   "Prioritize snips containing metric structures"
   
   :entropy-maximized
   "Choose next snip to maximize information gain"
   
   :triangle-chasing
   "Follow references to build triangle configurations"})

(defn walk-step [current-snip strategy seed]
  (case strategy
    :random-uniform
    (first (random-snips 1 (+ seed (hash (:id current-snip)))))
    
    :category-biased
    (let [weights {:category_theory 3 :math 2 :complexity 2 :other 1}
          sql "SELECT * FROM snips ORDER BY RANDOM() * 
               CASE category 
                 WHEN 'category_theory' THEN 3
                 WHEN 'math' THEN 2 
                 WHEN 'complexity' THEN 2
                 ELSE 1 END DESC LIMIT 1"]
      (first (query-snips sql)))
    
    :metric-seeking
    (first (extract-metric-snips (random-snips 10 seed)))))
```

## World Distance Functions

### Snip-Based Distance

```clojure
(defn snip-distance [s1 s2]
  "Distance between snips based on content similarity"
  (let [; Categorical distance
        cat-dist (if (= (:category s1) (:category s2)) 0 1)
        
        ; Lexical distance (Jaccard on tokens)
        tokens-1 (set (str/split (or (:latex s1) "") #"\s+"))
        tokens-2 (set (str/split (or (:latex s2) "") #"\s+"))
        jaccard (if (empty? (clojure.set/union tokens-1 tokens-2))
                  1.0
                  (- 1 (/ (count (clojure.set/intersection tokens-1 tokens-2))
                          (count (clojure.set/union tokens-1 tokens-2)))))
        
        ; Temporal distance (by ID ordering approximation)
        id-dist (Math/abs (- (hash (:id s1)) (hash (:id s2))))]
    
    ; Weighted combination
    (Math/sqrt (+ (* 0.3 cat-dist cat-dist)
                  (* 0.5 jaccard jaccard)
                  (* 0.2 (/ id-dist 1e9))))))
```

### World-Snip Bridge

```clojure
(defn world-from-snip [snip seed]
  "Create a PossibleWorld from a snip"
  {:seed (bit-xor seed (hash (:id snip)))
   :epoch (hash (:created_at snip))
   :category (:category snip)
   :latex-hash (hash (:latex snip))
   :invariants (extract-invariants (:latex snip))})

(defn extract-invariants [latex]
  "Extract mathematical invariants from LaTeX"
  (let [equations (re-seq #"\$\$[^$]+\$\$|\$[^$]+\$" (or latex ""))
        symbols (re-seq #"\\[a-zA-Z]+" (or latex ""))]
    {:equation-count (count equations)
     :symbol-set (set symbols)
     :has-inequality (boolean (re-find #"\\leq|\\geq|<|>" (or latex "")))}))
```

## Sparsification Algorithm

### Triangle Pruning

```clojure
(defn check-triangle [w1 w2 w3 distance-fn]
  "Check if triangle inequality holds and return slack"
  (let [d12 (distance-fn w1 w2)
        d23 (distance-fn w2 w3)
        d13 (distance-fn w1 w3)
        sum (+ d12 d23)]
    {:worlds [(:seed w1) (:seed w2) (:seed w3)]
     :distances {:d12 d12 :d23 d23 :d13 d13}
     :sum-d12-d23 sum
     :slack (- sum d13)
     :violated? (> d13 sum)
     :saturated? (< (Math/abs (- d13 sum)) 0.001)
     :redundant? (> (- sum d13) 1.0)})) ; High slack = redundant

(defn sparsify-world-graph [worlds distance-fn threshold]
  "Remove edges with high triangle slack"
  (let [; Build initial complete graph
        edges (for [w1 worlds w2 worlds :when (not= w1 w2)]
                {:from (:seed w1) :to (:seed w2) :dist (distance-fn w1 w2)})
        
        ; Check all triangles
        triangles (for [w1 worlds w2 worlds w3 worlds
                        :when (and (not= w1 w2) (not= w2 w3) (not= w1 w3))]
                    (check-triangle w1 w2 w3 distance-fn))
        
        ; Find redundant edges (high slack in many triangles)
        redundancy-scores (reduce (fn [scores tri]
                                    (if (:redundant? tri)
                                      (-> scores
                                          (update [(:from (:worlds tri) 0) (:from (:worlds tri) 2)]
                                                  (fnil inc 0)))
                                      scores))
                                  {}
                                  triangles)
        
        ; Keep only edges with low redundancy
        sparse-edges (filter (fn [e]
                               (< (get redundancy-scores [(:from e) (:to e)] 0) 
                                  threshold))
                             edges)]
    
    {:original-edge-count (count edges)
     :sparse-edge-count (count sparse-edges)
     :sparsity-ratio (/ (count sparse-edges) (count edges))
     :edges sparse-edges
     :removed (- (count edges) (count sparse-edges))}))
```

### Maximal Correct Sparsification

```clojure
(defn maximally-correct-sparsify [worlds distance-fn]
  "Find the sparsest graph that preserves all geodesics"
  (loop [threshold 1
         result nil]
    (let [sparse (sparsify-world-graph worlds distance-fn threshold)]
      (if (geodesics-preserved? sparse worlds distance-fn)
        ; Found valid sparsification, try sparser
        (if (< threshold 10)
          (recur (inc threshold) sparse)
          sparse)
        ; Too sparse, return previous
        (or result sparse)))))

(defn geodesics-preserved? [sparse-graph worlds distance-fn]
  "Check if shortest paths are preserved after sparsification"
  (let [sparse-edges (set (map (juxt :from :to) (:edges sparse-graph)))]
    (every? (fn [[w1 w2]]
              (let [original-dist (distance-fn w1 w2)
                    sparse-dist (shortest-path-length sparse-edges w1 w2 distance-fn)]
                (< (Math/abs (- original-dist sparse-dist)) 0.01)))
            (for [w1 worlds w2 worlds :when (not= w1 w2)] [w1 w2]))))
```

## GF(3) Conservation

```clojure
(defn trit-from-sparsification [sparse-result]
  "Map sparsification outcome to GF(3) trit"
  (let [ratio (:sparsity-ratio sparse-result)]
    (cond
      (< ratio 0.3) -1  ; Aggressive pruning (MINUS)
      (> ratio 0.7) +1  ; Minimal pruning (PLUS)
      :else 0)))        ; Balanced (ERGODIC)

(defn verify-gf3-conservation [path]
  "Verify GF(3) sum = 0 along path"
  (let [trits (map :trit path)]
    {:trits trits
     :sum (reduce + trits)
     :conserved? (zero? (mod (reduce + trits) 3))}))
```

## Canonical Triads

```
world-hopping (-1) ⊗ triangle-sparsifier (0) ⊗ glass-bead-game (+1) = 0 ✓
sheaf-cohomology (-1) ⊗ triangle-sparsifier (0) ⊗ ramanujan-expander (+1) = 0 ✓
moebius-inversion (-1) ⊗ triangle-sparsifier (0) ⊗ gay-mcp (+1) = 0 ✓
```

## Example Session

```clojure
;; Start random walk
(def snips (random-snips 20 69))
;; => [{:id "afba287b-..." :category "math" :latex "Theorem 2 (Geodesics..."}
;;     {:id "c5fa6db5-..." :category "category_theory" :latex "3.3 Factoring hypergraph..."}
;;     ...]

;; Extract metric structures
(def metric-snips (extract-metric-snips snips))
;; => [{:id "a3e1c5b8-..." :latex "Main Theorem A... d(Σ, E₋) + d(Σ, E₊) ≤ π"}]

;; Create worlds from snips
(def worlds (map #(world-from-snip % 69) metric-snips))

;; Sparsify
(def sparse (maximally-correct-sparsify worlds snip-distance))
;; => {:original-edge-count 380 :sparse-edge-count 127 :sparsity-ratio 0.334}

;; Navigate
(sparse-world-hop (first worlds) (last worlds) sparse)
;; => {:path [w1 w5 w12 w19] :hops 3 :efficiency 0.87}
```

## Mathematical Foundation

### Triangle Inequality as Pruning Criterion

From Riemannian manifold `(M, g)` with geodesic distance `d`:

```latex
d(x, z) ≤ d(x, y) + d(y, z)  ∀x, y, z ∈ M
```

Equality holds iff `y` lies on a geodesic from `x` to `z`.

**Sparsification principle**: If `d(x,z) << d(x,y) + d(y,z)`, the path through `y` is inefficient and edges `x→y` or `y→z` may be prunable.

### Snip Metric Space

The set of snips S with distance `d_snip` forms a **quasi-metric space**:

1. `d(s,s) = 0` ✓
2. `d(s,t) ≥ 0` ✓
3. `d(s,t) = d(t,s)` ✓ (symmetric)
4. `d(s,u) ≤ d(s,t) + d(t,u)` ✓ (triangle inequality by construction)

The random walk samples from this space, and sparsification finds minimal spanning subsets.

---

## End-of-Skill Interface

## Commands

```bash
# Random walk through snips
bb triangle_walk.bb --walk 10 --seed 69

# Extract metric snips
bb triangle_walk.bb --extract-metrics --limit 50

# Sparsify world graph
bb triangle_walk.bb --sparsify --threshold 3

# Check triangle inequality
bb triangle_walk.bb --check-triangle w1 w2 w3

# Maximal correct sparsification
bb triangle_walk.bb --max-sparse --preserve-geodesics

# Navigate sparse graph
bb triangle_walk.bb --navigate from_seed to_seed
```

## Integration with World Hopping

### Sparse World Navigation

```clojure
(defn sparse-world-hop [current-world target-world sparse-graph]
  "Navigate using sparsified world graph"
  (let [path (find-path-in-sparse-graph sparse-graph 
                                         (:seed current-world)
                                         (:seed target-world))]
    {:path path
     :hops (dec (count path))
     :total-distance (path-length path sparse-graph)
     :efficiency (/ (world-distance current-world target-world)
                    (path-length path sparse-graph))}))
```

### Snip-Guided Exploration

```clojure
(defn explore-via-snips [start-world n-steps seed]
  "Explore world space guided by snip random walk"
  (loop [current start-world
         step 0
         path [start-world]
         snips-visited []]
    (if (>= step n-steps)
      {:path path :snips snips-visited :steps step}
      (let [; Random walk to next snip
            next-snip (walk-step (last snips-visited) :metric-seeking (+ seed step))
            ; Create world from snip
            next-world (world-from-snip next-snip seed)
            ; Check triangle inequality with path
            valid? (every? (fn [w] 
                            (not (:violated? (check-triangle current w next-world snip-distance))))
                          (take-last 2 path))]
        (if valid?
          (recur next-world (inc step) (conj path next-world) (conj snips-visited next-snip))
          ; Triangle violation - try different snip
          (recur current (inc step) path snips-visited))))))
```

## Related Skills

- `world-hopping` — Possible world navigation
- `glass-bead-game` — Badiou triangle inequality
- `ramanujan-expander` — Spectral graph bounds
- `moebius-inversion` — Poset structure
- `gay-mcp` — Deterministic coloring

## References

- **Badiou, A.** - Being and Event (event ontology)
- **Kripke, S.** - Naming and Necessity (possible worlds)
- **Chung, F.** - Spectral Graph Theory (graph sparsification)
- **Spielman, D. & Teng, S.** - Spectral sparsification of graphs
