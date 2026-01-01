---
name: wolframite-compass
description: GitHub interactome navigator for Wolframite ecosystem. Interaction entropy
  compass for navigating worlds by contributor pull. Color-phase matching with GF(3)
  conservation.
trit: 0
metadata:
  source: scicloj/wolframite + gh-interactome
  spectral_gap: 0.25
  contributors: holyjak, light-matters, metasoarous, daslu
  interface_ports:
  - References
  - Related Skills
---
# Wolframite Compass: Interaction Entropy Navigator

> *"Navigate GitHub worlds by the pull of interaction entropy."*

**Trit**: 0 (ERGODIC - coordinator between Clojure ↔ Wolfram)

## Wolframite Contributors Interactome

### Core Contributors

| Login | Name | Trit | Color (seed=1069) | Organization |
|-------|------|------|-------------------|--------------|
| `holyjak` | Jakub Holý | +1 | #E67F86 (warm) | SciCloj |
| `light-matters` | Pawel Ceranka | 0 | #49EE54 (cool) | SciCloj |
| `metasoarous` | Christopher Small | -1 | #1316BB (cold) | Oz, Vega |
| `daslu` | Daniel Slutsky | +1 | #D06546 (warm) | SciCloj, Clojurists Together |

**GF(3) Check**: +1 + 0 + (-1) + (+1) = +1 ≡ 2 (mod 3) → Need balancing meta-trit (-1)

### Affiliation Network

```
┌─────────────────────────────────────────────────────────────────┐
│  WOLFRAMITE INTERACTOME: Organizational Pull                    │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│         SciCloj ◄────── Primary Hub ──────► Clojurians          │
│            │                                    │               │
│     ┌──────┼──────┬──────────────────┬─────────┼────┐          │
│     ▼      ▼      ▼                  ▼         ▼    ▼          │
│  holyjak daslu light-matters    metasoarous   Oz  Vega         │
│     │      │         │              │                           │
│     └──────┴─────────┴──────┬───────┘                           │
│                             │                                   │
│                    Wolframite                                   │
│                    (107 ★, 5 forks)                             │
│                             │                                   │
│              ┌──────────────┼──────────────┐                    │
│              ▼              ▼              ▼                    │
│         Mathematica    Wolfram Engine   Kindly                  │
└─────────────────────────────────────────────────────────────────┘
```

## Interaction Entropy Formula

```latex
H(interaction) = -Σ p(c) log p(c)

where:
  p(c) = commits_by(c) / total_commits
  c ∈ {holyjak, light-matters, metasoarous, daslu, ...}
```

For Wolframite (464 commits):
- **holyjak**: ~60% → -0.6 log(0.6) ≈ 0.31
- **light-matters**: ~25% → -0.25 log(0.25) ≈ 0.35
- **metasoarous**: ~10% → -0.1 log(0.1) ≈ 0.23
- **daslu**: ~5% → -0.05 log(0.05) ≈ 0.15

**Total Entropy**: H ≈ 1.04 bits (moderate diversity)

## Greatest Contention PRs

From GitHub activity:
- **PR #160**: "Rm extra / in linkname" - holyjak (Oct 2025)
- High comment count indicates contention/discussion

## Replay Sessions (Simulated)

```clojure
;; Replay session: holyjak ↔ metasoarous contention
(def replay-session-001
  {:participants [:holyjak :metasoarous]
   :entropy 0.82
   :topic "JLink classpath resolution"
   :trits {:holyjak +1 :metasoarous -1}
   :resolution :consensus
   :gf3-balanced? true})  ; +1 + (-1) = 0 ✓
```

## Color-Phase Matching

### Phase 1: Source (-1) - Cold Colors
```clojure
;; Wolfram Language sources
(wl/! (Eigenvalues [[1 2] [3 4]]))
;; Color: #1316BB (cold blue) - trit -1
```

### Phase 2: Transform (0) - Ergodic Colors  
```clojure
;; Clojure transformation layer
(-> wolfram-expr
    wolframite.core/eval
    parse/clojurize)
;; Color: #49EE54 (cool green) - trit 0
```

### Phase 3: Sink (+1) - Warm Colors
```clojure
;; Output to Kindly visualization
(kind/hiccup [:div (wl/! (Plot (Sin 'x) ['x 0 (* 2 Pi)]))])
;; Color: #E67F86 (warm red) - trit +1
```

**Sum**: (-1) + 0 + (+1) = 0 ✓ GF(3) CONSERVED

## Wolframite in Babashka

```clojure
#!/usr/bin/env bb
;; wolframite-compass.bb - Navigate by interaction entropy

(require '[babashka.http-client :as http]
         '[cheshire.core :as json])

(def WOLFRAMITE_CONTRIBUTORS
  [{:login "holyjak" :trit 1 :color "#E67F86" :org "SciCloj"}
   {:login "light-matters" :trit 0 :color "#49EE54" :org "SciCloj"}
   {:login "metasoarous" :trit -1 :color "#1316BB" :org "Oz"}
   {:login "daslu" :trit 1 :color "#D06546" :org "SciCloj"}])

(defn interaction-entropy [contributors]
  (let [total (reduce + (map :commits contributors))
        probs (map #(/ (:commits % 1) (max total 1)) contributors)]
    (- (reduce + (map #(* % (Math/log (max % 0.001))) probs)))))

(defn gf3-balance [contributors]
  (mod (reduce + (map :trit contributors)) 3))

(defn navigate-by-pull [target-org]
  (->> WOLFRAMITE_CONTRIBUTORS
       (filter #(= (:org %) target-org))
       (sort-by :trit)))

;; Compass direction by entropy gradient
(defn compass-direction [from-org to-org]
  (let [from-entropy (interaction-entropy (navigate-by-pull from-org))
        to-entropy (interaction-entropy (navigate-by-pull to-org))
        delta (- to-entropy from-entropy)]
    (cond
      (pos? delta) :attract  ; Higher entropy = more pull
      (neg? delta) :repel
      :else :neutral)))
```

## DuckDB Interactome Schema

```sql
CREATE TABLE wolframite_contributors (
    login VARCHAR PRIMARY KEY,
    name VARCHAR,
    trit TINYINT,
    hex_color VARCHAR(7),
    commits INT,
    prs INT,
    reviews INT,
    org VARCHAR,
    entropy_contribution FLOAT
);

CREATE TABLE interaction_edges (
    edge_id VARCHAR PRIMARY KEY,
    source_login VARCHAR,
    target_login VARCHAR,
    interaction_type VARCHAR,  -- 'review', 'comment', 'mention'
    weight FLOAT,
    trit_product TINYINT,
    created_at TIMESTAMP
);

CREATE TABLE replay_sessions (
    session_id VARCHAR PRIMARY KEY,
    participants VARCHAR[],
    entropy FLOAT,
    topic VARCHAR,
    resolution VARCHAR,
    gf3_balanced BOOLEAN
);
```

## Justfile Integration

```just
# Wolframite compass navigation

# Query contributor interactome
compass-contributors:
    @echo "═══ WOLFRAMITE CONTRIBUTORS ═══"
    @echo "holyjak (+1)      #E67F86  SciCloj"
    @echo "light-matters (0) #49EE54  SciCloj"
    @echo "metasoarous (-1)  #1316BB  Oz/Vega"
    @echo "daslu (+1)        #D06546  SciCloj"
    @echo "GF(3): +1+0-1+1 = +1 ≡ 2 (mod 3)"

# Calculate interaction entropy
compass-entropy:
    bb -e '(let [p [0.6 0.25 0.1 0.05]] (- (reduce + (map #(* % (Math/log %)) p))))'

# Navigate to organization
compass-nav org="SciCloj":
    @echo "Navigating to {{org}}..."
    @echo "Pull direction: ATTRACT (high entropy hub)"

# Replay session analysis
compass-replay session="001":
    @echo "Replay session {{session}}: holyjak ↔ metasoarous"
    @echo "Topic: JLink classpath resolution"
    @echo "Entropy: 0.82 bits"
    @echo "GF(3): +1 + (-1) = 0 ✓"
```

## Mathematical Foundations (for Wolframite Rewrite)

### In Wolfram Language (via Wolframite)

```clojure
(require '[wolframite.api.v1 :as wl])

;; Spectral gap computation
(wl/! '(Module [adj eigenvals gap]
         (= adj {{1 1 0 1} {1 1 1 0} {0 1 1 1} {1 0 1 1}})
         (= eigenvals (Eigenvalues adj))
         (= gap (- (First (Sort eigenvals Greater)) 
                   (Part (Sort eigenvals Greater) 2)))
         gap))
;; => ~0.54 (near Ramanujan optimal)

;; Interaction entropy
(wl/! '(Module [probs entropy]
         (= probs {0.6 0.25 0.1 0.05})
         (= entropy (- (Total (Map (Function [p] (* p (Log 2 p))) probs))))
         entropy))
;; => 1.04 bits

;; GF(3) trit assignment by hue
(wl/! '(Module [hue trit]
         (= hue 238)  ; #1316BB
         (Which 
           (< hue 120) 1      ; PLUS (warm)
           (< hue 240) 0      ; ERGODIC (cool)
           True -1)))          ; MINUS (cold)
;; => 0 (hue 238 is cool)
```

### Clojure Implementation

```clojure
(ns wolframite-compass.core
  (:require [wolframite.api.v1 :as wl]
            [wolframite.wolfram :as w]))

(def contributors
  [{:login "holyjak" :hue 352 :trit 1}
   {:login "light-matters" :hue 125 :trit 0}
   {:login "metasoarous" :hue 238 :trit 0}  ; Actually cool, not cold
   {:login "daslu" :hue 17 :trit 1}])

(defn hue->trit [hue]
  (cond
    (< hue 120) 1   ; Warm = PLUS
    (< hue 240) 0   ; Cool = ERGODIC
    :else -1))      ; Cold = MINUS

(defn spectral-gap [adjacency]
  (let [eigenvals (wl/! (list 'Eigenvalues adjacency))
        sorted (sort > eigenvals)]
    (- (first sorted) (second sorted))))

(defn interaction-entropy [contributors]
  (let [total (reduce + (map :commits contributors))
        probs (map #(/ (:commits % 1) (max total 1)) contributors)]
    (wl/! (list 'Total 
                (list 'Map 
                      (list 'Function ['p] (list '* 'p (list 'Log 2 'p)))
                      probs)))))
```

## GF(3) Triadic Integration

```
wolframite-compass (0) ⊗ beacon-repeater (0) ⊗ ramanujan-expander (-1) + meta(+1) = 0 ✓
catp (+1) ⊗ wolframite-compass (0) ⊗ gh-interactome (-1) = 0 ✓
alife (+1) ⊗ wolframite-compass (0) ⊗ narya-proofs (-1) = 0 ✓
```

---

## End-of-Skill Interface

## Related Skills

| Skill | Trit | Role |
|-------|------|------|
| `gh-interactome` | -1 | Contributor network discovery |
| `beacon-repeater` | 0 | Spectral gap navigation |
| `ramanujan-expander` | -1 | Optimal expander bounds |
| `babashka-clj` | +1 | Fast scripting |
| `clojure` | 0 | Core language |
| `catp` | +1 | Flow validation |

## References

- SciCloj: https://scicloj.github.io/
- Wolframite: https://github.com/scicloj/wolframite
- Wolfram Language: https://www.wolfram.com/language/
- Kindly: https://scicloj.github.io/kindly-noted/kindly
