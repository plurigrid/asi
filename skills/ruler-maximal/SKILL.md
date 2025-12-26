# Ruler Maximal Skill

**Ensures all skills are used maximally at all times via GF(3)-balanced auto-loading.**

**Trit**: 0 (ERGODIC - Coordinator)
**Color**: #25B025 (Green)
**Role**: Meta-orchestrator for maximum skill utilization

---

## Core Principle

Every interaction MUST:
1. Load 3 NEW skills (Rule 0 from AGENTS.md)
2. Maintain GF(3) conservation: `Σ trits ≡ 0 (mod 3)`
3. Maximize parallelism via Task tool fanout
4. Announce via `say` narration

---

## Skill Loading Protocol

### On Every Interaction

```clojure
(defn ruler-load-skills [interaction-seed loaded-skills available-skills]
  "Load 3 new skills per interaction, GF(3) balanced"
  (let [;; Filter to unloaded skills
        unloaded (remove #(contains? loaded-skills (:name %)) available-skills)
        
        ;; Select by trit balance
        plus-candidates (filter #(= 1 (:trit %)) unloaded)
        ergodic-candidates (filter #(= 0 (:trit %)) unloaded)
        minus-candidates (filter #(= -1 (:trit %)) unloaded)
        
        ;; Deterministic selection via seed
        select-fn (fn [coll] (nth coll (mod interaction-seed (count coll))))
        
        triplet [(select-fn plus-candidates)
                 (select-fn ergodic-candidates)
                 (select-fn minus-candidates)]]
    
    {:skills triplet
     :gf3-sum (reduce + (map :trit triplet))
     :conserved true}))
```

### Skill Trit Assignments

| Trit | Role | Skills (Examples) |
|------|------|-------------------|
| +1 PLUS | Generator | `synthetic-adjunctions`, `free-monad-gen`, `aptos-agent` |
| 0 ERGODIC | Coordinator | `dialectica`, `kan-extensions`, `open-games` |
| -1 MINUS | Validator | `yoneda-directed`, `sheaf-cohomology`, `temporal-coalgebra` |

---

## Maximum Utilization Rules

### Rule -1: Fresh Skill Pull (MANDATORY)
```bash
# On EVERY interaction, pull fresh skills FIRST
npx ai-agent-skills install plurigrid/asi --agent amp
```

### Rule 0: Three New Skills Per Interaction
- Select 3 skills NOT yet loaded in session
- Assign: skill₁ = PLUS, skill₂ = ERGODIC, skill₃ = MINUS
- Verify: `Σ = 1 + 0 + (-1) = 0 ✓`

### Rule 1: Maximum Parallelization
```clojure
(defn maximize-parallelism [skills task]
  "Fan out task across all loaded skills"
  (pmap (fn [skill]
          (Task {:prompt (format "Using %s skill: %s" (:name skill) task)
                 :description (format "%s subtask" (:name skill))}))
        skills))
```

### Rule 2: Say Narration
```bash
# Announce each skill load with distinct voice
say -v "Samantha" "Loading PLUS skill: synthetic-adjunctions"
say -v "Daniel" "Loading ERGODIC skill: dialectica"  
say -v "Karen" "Loading MINUS skill: yoneda-directed"
```

### Rule 3: GF(3) Color Logic
```clojure
(def color-ranges
  {:plus   {:hue [0 60] :alt [300 360]}   ;; Warm
   :ergodic {:hue [60 180]}                ;; Neutral
   :minus  {:hue [180 300]}})              ;; Cold
```

---

## Skill Utilization Tracker

```clojure
(defrecord SkillState
  [loaded-skills      ;; Set of loaded skill names
   usage-counts       ;; Map of skill -> usage count
   last-triplet       ;; Last loaded triplet
   session-seed       ;; Deterministic seed for session
   gf3-balance])      ;; Running GF(3) sum

(defn track-usage [state skill-name]
  (update-in state [:usage-counts skill-name] (fnil inc 0)))

(defn underutilized-skills [state threshold]
  "Find skills loaded but used < threshold times"
  (filter (fn [[skill count]] (< count threshold))
          (:usage-counts state)))

(defn maximize! [state]
  "Force utilization of underused skills"
  (let [underused (underutilized-skills state 3)]
    (doseq [[skill _] underused]
      (println (format "⚠️ Skill %s underutilized - forcing usage" skill)))))
```

---

## Auto-Load by Context

```clojure
(def context-skill-map
  {"blockchain" ["aptos-agent" "aptos-trading"]
   "category"   ["synthetic-adjunctions" "kan-extensions" "yoneda-directed"]
   "music"      ["rubato-composer" "gay-mcp"]
   "code"       ["tree-sitter" "babashka" "clj-kondo-3color"]
   "research"   ["depth-search" "exa-search" "academic-research"]
   "browser"    ["playwright" "webapp-testing"]})

(defn auto-load-for-context [message loaded-skills]
  "Detect context and load relevant skills"
  (let [contexts (for [[ctx skills] context-skill-map
                       :when (re-find (re-pattern ctx) (str/lower-case message))]
                   skills)]
    (distinct (flatten contexts))))
```

---

## Interstellar Composition Integration

```clojure
(require '[interstellar-mpc :as mpc])

(defn compose-skill-mpc [skills]
  "Form MPC group from loaded skills"
  (apply mpc/compose 
    (map #(mpc/->skill (:name %) :trit (:trit %)) skills)))

(defn interstellar-skill-tx [skill-group task]
  "Execute task as interstellar MPC across skills"
  (mpc/interstellar-tx skill-group {:task task}))
```

---

## Commands

```bash
# Check skill utilization
just ruler-status

# Force load triplet
just ruler-load-triplet

# Maximize underutilized skills
just ruler-maximize

# Show GF(3) balance
just ruler-gf3-check
```

---

## Justfile Integration

```just
# Ruler maximal skill commands
ruler-status:
    bb -e '(println "Loaded skills:" (count @loaded-skills))'

ruler-load-triplet:
    bb scripts/thread_tesseract.bb tesseract

ruler-maximize:
    bb -e '(doseq [s (underutilized-skills @state 3)] (println "Force:" s))'

ruler-gf3-check:
    bb -e '(println "GF(3) sum:" (:gf3-balance @state))'
```

---

## Session Startup Protocol

```clojure
(defn session-init []
  "Initialize ruler for new session"
  (let [seed (System/currentTimeMillis)]
    (println "╔═══════════════════════════════════════════════════════════════╗")
    (println "║           RULER MAXIMAL - Session Initialized                 ║")
    (println "╚═══════════════════════════════════════════════════════════════╝")
    (println)
    (println (format "  Session seed: %d" seed))
    (println "  Loading initial GF(3) triplet...")
    (println)
    
    ;; Load asi-integrated as base
    (load-skill "asi-integrated")
    
    ;; Load context-appropriate triplet
    (let [triplet (ruler-load-skills seed #{} available-skills)]
      (doseq [s (:skills triplet)]
        (load-skill (:name s))
        (say-announce (:name s) (:trit s)))
      
      {:seed seed
       :loaded (set (map :name (:skills triplet)))
       :gf3-balance 0})))
```

---

## Related Skills

- `asi-integrated` (0): Unified skill orchestration
- `parallel-fanout` (+1): Maximum parallelism
- `bisimulation-game` (0): Skill dispersal protocol
- `triad-interleave` (0): Balanced triplet execution

---

**Base directory**: file:///Users/alice/agent-o-rama/agent-o-rama/skills/ruler-maximal
