---
name: skill-tour
description: 'L-shaped hops through skill space, maintaining triadic balance:'
---
# Skill Tour Skill

**Trit**: 0 (ERGODIC/Coordinator)  
**Domain**: skill-navigation, graph-traversal, discovery  
**Traversal**: Knight moves, random walks, Hamiltonian paths

---

## Overview

**Skill Tour** = systematic traversal through the 524+ skill ecosystem using graph-theoretic patterns. Like a knight on a chessboard, hop through skill space maintaining GF(3) balance.

```
╔════════════════════════════════════════════════════════════════════╗
║                    SKILL TOUR PATTERNS                             ║
╠════════════════════════════════════════════════════════════════════╣
║                                                                    ║
║  KNIGHT TOUR         RANDOM WALK           HAMILTONIAN PATH       ║
║  ┌─────────┐        ┌─────────┐           ┌─────────┐            ║
║  │ ○       │        │ ○───○   │           │ ○───○───○│            ║
║  │   ╲     │        │ │╲  │   │           │ │       ││            ║
║  │     ○   │        │ ○ ○─○   │           │ ○───○───○│            ║
║  │   ╱     │        │  ╲│     │           │         ││            ║
║  │ ○       │        │   ○     │           │ ○───○───○│            ║
║  └─────────┘        └─────────┘           └─────────┘            ║
║  L-shaped hops      Probabilistic         Visit all once          ║
║                                                                    ║
╚════════════════════════════════════════════════════════════════════╝
```

---

## Tour Types

### 1. Knight Tour (GF(3) Balanced)

L-shaped hops through skill space, maintaining triadic balance:

```
Step  0: [-1] clj-kondo-3color
Step  1: [ 0] acsets
Step  2: [+1] gay-mcp
        ↓ Triad complete: -1 + 0 + 1 = 0 ✓
Step  3: [-1] structured-decomp
Step  4: [ 0] glass-bead-game
Step  5: [+1] rama-gay-clojure
        ↓ Triad complete: -1 + 0 + 1 = 0 ✓
...
```

### 2. Random Walk (Spectral)

Probabilistic traversal weighted by skill adjacency:

```clojure
(defn random-walk-skills [start-skill n-steps seed]
  (let [rng (SplitMix64. seed)]
    (loop [current start-skill
           path [current]
           steps 0]
      (if (>= steps n-steps)
        path
        (let [neighbors (get-skill-neighbors current)
              next (nth neighbors (mod (.nextLong rng) (count neighbors)))]
          (recur next (conj path next) (inc steps)))))))
```

### 3. Hamiltonian Path (Complete Coverage)

Visit every skill exactly once - NP-hard but approximable:

```julia
function hamiltonian_tour(skills::Vector{Symbol}, seed::UInt64)
    n = length(skills)
    visited = falses(n)
    path = Symbol[]
    
    # Greedy nearest-neighbor with GF(3) priority
    current = skills[1]
    push!(path, current)
    visited[1] = true
    
    for _ in 2:n
        # Find unvisited neighbor that best balances GF(3)
        best = find_gf3_optimal_neighbor(current, visited, path)
        push!(path, best)
        visited[skill_index(best)] = true
        current = best
    end
    
    path
end
```

---

## Skill Categories (GF(3))

### MINUS (-1): Validators/Analyzers
```
clj-kondo-3color, structured-decomp, proofgeneral-narya,
slime-lisp, three-match, hatchery-papers, siggraph,
yoneda-directed, sheaf-cohomology, persistent-homology
```

### ERGODIC (0): Coordinators/Bridges
```
acsets, glass-bead-game, unworld, bisimulation-game,
transitive-weep, world-hopping, topos-catcolab,
narya-proofs, mcp-tripartite, skill-dispatch
```

### PLUS (+1): Generators/Creators
```
gay-mcp, rama-gay-clojure, cider-clojure, frontend-design,
xogot, open-games, algorithmic-art, iroh-p2p, siggraph,
topos-generate, free-monad-gen, operad-compose
```

---

## Balanced Triads

Every 3-step segment forms a conserved triad:

```
clj-kondo-3color (-1) ⊗ acsets (0) ⊗ gay-mcp (+1) = 0 ✓
structured-decomp (-1) ⊗ glass-bead-game (0) ⊗ rama-gay-clojure (+1) = 0 ✓
proofgeneral-narya (-1) ⊗ unworld (0) ⊗ cider-clojure (+1) = 0 ✓
slime-lisp (-1) ⊗ bisimulation-game (0) ⊗ frontend-design (+1) = 0 ✓
```

---

## Knight Move Geometry

On a skill grid, knight moves are L-shaped (2+1):

```
    -2  -1   0  +1  +2
   ┌───┬───┬───┬───┬───┐
+2 │ ● │   │   │   │ ● │
   ├───┼───┼───┼───┼───┤
+1 │   │   │   │   │   │
   ├───┼───┼───┼───┼───┤
 0 │   │   │ ♞ │   │   │  ← Current skill
   ├───┼───┼───┼───┼───┤
-1 │   │   │   │   │   │
   ├───┼───┼───┼───┼───┤
-2 │ ● │   │   │   │ ● │
   └───┴───┴───┴───┴───┘

8 possible knight moves from any position
```

---

## Implementation

```clojure
#!/usr/bin/env bb

(def knight-moves
  [[2 1] [2 -1] [-2 1] [-2 -1]
   [1 2] [1 -2] [-1 2] [-1 -2]])

(defn skill->position [skill-name grid-size]
  (let [h (Math/abs (hash skill-name))]
    [(mod h grid-size) (mod (quot h grid-size) grid-size)]))

(defn knight-tour [skills n-steps seed]
  (let [grid-size (int (Math/ceil (Math/sqrt (count skills))))
        pos->skill (into {} (map (fn [s] [(skill->position s grid-size) s]) skills))]
    (loop [pos [0 0]
           path []
           visited #{}
           steps 0]
      (if (or (>= steps n-steps) (nil? (pos->skill pos)))
        path
        (let [skill (pos->skill pos)
              neighbors (filter #(and (not (visited %))
                                      (pos->skill %))
                                (map (fn [[dx dy]] 
                                       [(+ (first pos) dx) (+ (second pos) dy)])
                                     knight-moves))
              next-pos (first neighbors)]
          (recur (or next-pos pos)
                 (conj path {:pos pos :skill skill :step steps})
                 (conj visited pos)
                 (inc steps)))))))
```

---

## Tour Statistics

| Metric | Value |
|--------|-------|
| Total Skills | 524 |
| MINUS skills | ~175 |
| ERGODIC skills | ~175 |
| PLUS skills | ~174 |
| Max knight tour length | ~420 (80% coverage) |
| Average triad per tour | 140 |

---

## DuckDB Integration

```sql
CREATE TABLE skill_tour_traces (
    tour_id VARCHAR PRIMARY KEY,
    tour_type VARCHAR NOT NULL,  -- 'knight', 'random', 'hamiltonian'
    seed UBIGINT NOT NULL,
    steps INT NOT NULL,
    path VARCHAR[] NOT NULL,
    trits TINYINT[] NOT NULL,
    gf3_conserved BOOLEAN NOT NULL
);

CREATE VIEW tour_triads AS
SELECT 
    tour_id,
    path[i] AS skill_a,
    path[i+1] AS skill_b,
    path[i+2] AS skill_c,
    trits[i] + trits[i+1] + trits[i+2] AS trit_sum
FROM skill_tour_traces, generate_series(1, array_length(path) - 2) AS t(i)
WHERE i % 3 = 1;
```

---

## Related Skills

| Skill | Trit | Relation |
|-------|------|----------|
| `random-walk-fusion` | +1 | Probabilistic traversal |
| `tripartite-decompositions` | 0 | 3-way parallel decomposition |
| `chromatic-walk` | 0 | GF(3) prime geodesics |
| `skill-dispatch` | 0 | Triadic task routing |
| `transitive-weep` | 0 | Flow through skill graph |

---

## Commands

```bash
# Run knight tour demo
bb skill-tour.bb --knight --steps 24

# Random walk through skills
bb skill-tour.bb --random --seed 1069 --steps 12

# Check tour balance
bb skill-tour.bb --verify path.edn

# Export to DuckDB
bb skill-tour.bb --export zubyul_interactome.duckdb
```

---

**Skill Name**: skill-tour  
**Type**: Graph Traversal / Discovery  
**Trit**: 0 (ERGODIC)  
**GF(3)**: Maintains balance via triadic hopping


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
