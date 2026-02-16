#!/usr/bin/env bb

;; skill-taxonomy registry.bb
;; 69-Skill registry with search, discovery, and GF(3) validation
;; Pattern: npm registry + Hackage + AlphaGo ELO ranking

(require '[clojure.string :as str])

;; ============================================================================
;; REGISTRY DATA STRUCTURE
;; ============================================================================

(def SKILL_REGISTRY
  {
   ;; TIER 1: FOUNDATIONAL PRIMITIVES (Blooming 🌸)
   :gay-mcp
   {:name "gay-mcp"
    :version "1.0.0"
    :description "Deterministic color generation with SplitMix64 + GF(3)"
    :keywords ["color" "mcp" "deterministic" "gf3"]
    :trit 1
    :color "#FF6B35"
    :category "foundation"
    :completion 0.95
    :ie-score 0.10
    :authors [{:name "bmorphism" :email "core@bmorphism.ai"}]
    :homepage "https://github.com/bmorphism/Gay.jl"
    :license "MIT"}

   :acsets
   {:name "acsets"
    :version "1.0.0"
    :description "Algebraic Attributed C-Sets for categorical data structures"
    :keywords ["category-theory" "acset" "algebra" "data-structure"]
    :trit 0
    :color "#20B2AA"
    :category "foundation"
    :completion 0.92
    :ie-score 0.12
    :authors [{:name "bmorphism" :email "core@bmorphism.ai"}]
    :homepage "https://github.com/AlgebraicJulia/ACSets.jl"
    :license "MIT"}

   :gay-julia
   {:name "gay-julia"
    :version "1.0.0"
    :description "Wide-gamut color sampling with Julia + GPU support"
    :keywords ["color" "julia" "gpu" "continuous-spectrum"]
    :trit -1
    :color "#87CEEB"
    :category "foundation"
    :completion 0.88
    :ie-score 0.14
    :authors [{:name "bmorphism" :email "core@bmorphism.ai"}]
    :homepage "https://github.com/bmorphism/Gay.jl"
    :license "MIT"}

   :autopoiesis
   {:name "autopoiesis"
    :version "1.0.0"
    :description "Self-modifying AI agent configuration via ruler + MCP + DuckDB"
    :keywords ["autopoiesis" "self-modifying" "agent" "varela"]
    :trit 1
    :color "#FF8C42"
    :category "foundation"
    :completion 0.85
    :ie-score 0.08
    :authors [{:name "bmorphism" :email "core@bmorphism.ai"}]
    :homepage "https://github.com/bmorphism/autopoiesis"
    :license "MIT"}

   ;; TIER 2: STRUCTURAL ENABLERS (Stepping 🌉)
   :skill-dispatch
   {:name "skill-dispatch"
    :version "0.8.0"
    :description "Central routing mechanism for triadic skill execution"
    :keywords ["dispatch" "routing" "orchestration" "triad"]
    :trit 0
    :color "#FFFFFF"
    :category "structural"
    :completion 0.65
    :ie-score 0.35
    :authors [{:name "bmorphism"}]
    :homepage "https://github.com/plurigrid/duck"
    :license "MIT"}

   :world-hopping
   {:name "world-hopping"
    :version "0.7.0"
    :description "Navigation through possibility space with state branching"
    :keywords ["world" "hopping" "exploration" "branching"]
    :trit 1
    :color "#FFA500"
    :category "structural"
    :completion 0.55
    :ie-score 0.38
    :authors [{:name "bmorphism"}]
    :homepage "https://github.com/plurigrid/world-hopping"
    :license "MIT"}

   :triad-interleave
   {:name "triad-interleave"
    :version "0.6.0"
    :description "Interleaves three deterministic color streams in parallel"
    :keywords ["triad" "interleave" "parallelism" "scheduling"]
    :trit 1
    :color "#FFB84D"
    :category "structural"
    :completion 0.50
    :ie-score 0.42
    :authors [{:name "bmorphism"}]
    :homepage "https://github.com/plurigrid/duck"
    :license "MIT"}

   :bisimulation-game
   {:name "bisimulation-game"
    :version "0.5.0"
    :description "Attacker/Defender/Arbiter game for distributed verification"
    :keywords ["bisimulation" "game-theory" "verification" "security"]
    :trit -1
    :color "#4671D5"
    :category "structural"
    :completion 0.40
    :ie-score 0.68
    :authors [{:name "bmorphism"}]
    :homepage "https://github.com/plurigrid/bisimulation-game"
    :license "MIT"}

   ;; TIER 3: EMERGENT (Sad 😢)
   :cognitive-surrogate
   {:name "cognitive-surrogate"
    :version "0.3.0"
    :description "Layer 6: Psychological profiling of agent behavior"
    :keywords ["cognition" "psychology" "behavior" "surrogate"]
    :trit 0
    :color "#FFFFFF"
    :category "emergent"
    :completion 0.30
    :ie-score 0.62
    :authors [{:name "barton" :email "barton@anthropic.com"}]
    :homepage "https://github.com/plurigrid/cognitive-surrogate"
    :license "MIT"}

   :influence-propagation
   {:name "influence-propagation"
    :version "0.2.0"
    :description "Layer 7: Network dynamics and influence propagation"
    :keywords ["influence" "propagation" "network" "dynamics"]
    :trit -1
    :color "#6495ED"
    :category "emergent"
    :completion 0.25
    :ie-score 0.65
    :authors [{:name "barton" :email "barton@anthropic.com"}]
    :homepage "https://github.com/plurigrid/influence-propagation"
    :license "MIT"}

   :world-memory-worlding
   {:name "world-memory-worlding"
    :version "0.2.0"
    :description "Combines world-hopping + temporal federation with snapshots"
    :keywords ["world" "memory" "temporal" "federation"]
    :trit 0
    :color "#FFFFFF"
    :category "emergent"
    :completion 0.20
    :ie-score 0.72
    :authors [{:name "bmorphism"}]
    :homepage "https://github.com/plurigrid/world-memory-worlding"
    :license "MIT"}

   :asi-polynomial-operads
   {:name "asi-polynomial-operads"
    :version "0.1.0"
    :description "Pattern-runs-on-matter duality via free/cofree monads"
    :keywords ["polynomial" "operad" "category-theory" "pattern"]
    :trit 1
    :color "#FF1493"
    :category "emergent"
    :completion 0.15
    :ie-score 0.85
    :authors [{:name "bmorphism"}]
    :homepage "https://github.com/plurigrid/asi-polynomial-operads"
    :license "MIT"}

   ;; TIER 4: META-LEVEL (Sad 😢)
   :unwiring-arena
   {:name "unwiring-arena"
    :version "0.1.0"
    :description "Meta-learning through constraint release + play"
    :keywords ["unwiring" "arena" "learning" "constraints"]
    :trit 0
    :color "#FFFFFF"
    :category "meta"
    :completion 0.10
    :ie-score 0.75
    :authors [{:name "barton"}]
    :homepage "https://github.com/plurigrid/unwiring-arena"
    :license "MIT"}

   :agent-o-rama
   {:name "agent-o-rama"
    :version "0.1.0"
    :description "Distributed orchestration of 26+ agents at scale"
    :keywords ["agent" "orchestration" "distributed" "coordination"]
    :trit 1
    :color "#FF2E63"
    :category "meta"
    :completion 0.08
    :ie-score 0.70
    :authors [{:name "bmorphism"}]
    :homepage "https://github.com/plurigrid/agent-o-rama"
    :license "MIT"}

   ;; TOP 10 SAD STATE (Need code-context)
   :skill-taxonomy
   {:name "skill-taxonomy"
    :version "0.0.1"
    :description "69-skill organization + discovery system"
    :keywords ["registry" "discovery" "taxonomy" "metadata"]
    :trit -1
    :color "#0000CD"
    :category "meta"
    :completion 0.05
    :ie-score 0.90
    :authors [{:name "bmorphism"}]
    :homepage "https://github.com/plurigrid/asi-skills"
    :license "MIT"}

   :llms-txt-discovery
   {:name "llms-txt-discovery"
    :version "0.0.1"
    :description "Largest AI documentation directory with crawling + indexing"
    :keywords ["documentation" "crawling" "indexing" "llms"]
    :trit 0
    :color "#0000FF"
    :category "meta"
    :completion 0.02
    :ie-score 0.90
    :authors [{:name "bmorphism"}]
    :homepage "https://github.com/plurigrid/llms-txt-hub"
    :license "MIT"}

   :documentation-indexing
   {:name "documentation-indexing"
    :version "0.0.1"
    :description "Searchable documentation for all 69 skills"
    :keywords ["documentation" "search" "indexing" "discovery"]
    :trit 1
    :color "#0000FF"
    :category "meta"
    :completion 0.01
    :ie-score 0.87
    :authors [{:name "bmorphism"}]
    :homepage "https://github.com/plurigrid/documentation-indexing"
    :license "MIT"}
  })

;; ============================================================================
;; SEARCH FUNCTIONS
;; ============================================================================

(defn search-by-name
  "Search skills by name (prefix match)"
  [registry query]
  (let [q (str/lower-case query)]
    (filter #(str/starts-with? (str/lower-case (:name (val %))) q)
            registry)))

(defn search-by-keyword
  "Search skills by keyword (contains match)"
  [registry query]
  (let [q (str/lower-case query)]
    (filter #(some (fn [kw] (str/includes? (str/lower-case kw) q))
                   (:keywords (val %)))
            registry)))

(defn search-by-trit
  "Search skills by trit assignment"
  [registry trit]
  (filter #(= (:trit (val %)) trit) registry))

(defn search-by-category
  "Search skills by category"
  [registry category]
  (filter #(= (:category (val %)) category) registry))

(defn search-by-completion
  "Search skills by completion range"
  [registry min-completion max-completion]
  (filter #(let [c (:completion (val %))]
             (and (>= c min-completion) (<= c max-completion)))
          registry))

(defn search
  "Universal search function"
  [registry {:keys [query type trit category completion-min completion-max]
             :or {completion-min 0 completion-max 1}}]
  (cond
    query
    (case type
      :name (search-by-name registry query)
      :keyword (search-by-keyword registry query)
      nil (concat (search-by-name registry query)
                  (search-by-keyword registry query)))

    trit
    (search-by-trit registry trit)

    category
    (search-by-category registry category)

    :else
    (search-by-completion registry completion-min completion-max)))

;; ============================================================================
;; RANKING & METRICS
;; ============================================================================

(defn by-completion
  "Rank skills by completion (highest first)"
  [skills]
  (sort-by #(- (:completion (val %))) skills))

(defn by-ie-score
  "Rank skills by information energy (highest first)"
  [skills]
  (sort-by #(- (:ie-score (val %))) skills))

(defn by-gf3-trit
  "Group skills by GF(3) trit balance"
  [registry]
  {:validators (search-by-trit registry -1)
   :coordinators (search-by-trit registry 0)
   :generators (search-by-trit registry 1)})

;; ============================================================================
;; GF(3) VALIDATION
;; ============================================================================

(defn verify-gf3-balance
  "Verify GF(3) conservation: sum(trits) ≡ 0 (mod 3)"
  [registry]
  (let [trits (map #(:trit (val %)) registry)
        sum (reduce + 0 trits)
        balanced? (= (mod sum 3) 0)]
    {:sum sum
     :balanced? balanced?
     :error (if-not balanced?
              (str "GF(3) violation: sum=" sum " (not ≡ 0 mod 3)")
              nil)}))

;; ============================================================================
;; CLI INTERFACE
;; ============================================================================

(defn print-skill
  "Pretty-print a skill entry"
  [skill]
  (let [{:keys [name version description trit color completion ie-score]} skill]
    (printf "%-30s v%-8s [trit=%2d] [%s] IE:%.2f\n"
            (str name)
            (str version)
            trit
            (str/replace color #"^#" "")
            ie-score)))

(defn list-all-skills
  "List all skills with metadata"
  [registry]
  (println "\n══════════════════════════════════════════════════════════════════")
  (println " 69-SKILL TAXONOMY REGISTRY")
  (println "══════════════════════════════════════════════════════════════════")
  (doseq [[_ skill] (sort-by #(:name (val %)) registry)]
    (print-skill skill))
  (let [balance (verify-gf3-balance registry)
        count (count registry)]
    (println "══════════════════════════════════════════════════════════════════")
    (printf " Total: %d skills | GF(3) sum=%d | %s\n"
            count
            (:sum balance)
            (if (:balanced? balance) "✓ BALANCED" "✗ VIOLATION"))))

(defn show-registry-summary
  "Show registry statistics"
  [registry]
  (let [by-trit (group-by #(:trit (val %)) registry)
        by-completion (group-by #(if (>= (:completion (val %)) 0.8) "blooming"
                                   (if (>= (:completion (val %)) 0.3) "stepping"
                                     "sad"))
                                registry)
        balance (verify-gf3-balance registry)]
    (println "\n📊 REGISTRY STATISTICS")
    (println "────────────────────────")
    (printf "Total Skills: %d\n" (count registry))
    (printf "Validators (-1):   %d\n" (count (get by-trit -1 [])))
    (printf "Coordinators (0):  %d\n" (count (get by-trit 0 [])))
    (printf "Generators (+1):   %d\n" (count (get by-trit 1 [])))
    (println "")
    (printf "Blooming (0.8+):   %d\n" (count (get by-completion "blooming" [])))
    (printf "Stepping (0.3+):   %d\n" (count (get by-completion "stepping" [])))
    (printf "Sad (< 0.3):       %d\n" (count (get by-completion "sad" [])))
    (println "")
    (printf "GF(3) Balance: %s (sum=%d)\n"
            (if (:balanced? balance) "✓" "✗")
            (:sum balance))))

(defn handle-cli
  "Handle command-line arguments"
  [args]
  (cond
    (= args ["list"])
    (list-all-skills SKILL_REGISTRY)

    (= args ["stats"])
    (show-registry-summary SKILL_REGISTRY)

    (and (>= (count args) 2) (= (first args) "search"))
    (let [query (second args)]
      (println (str "\n🔍 Search results for '" query "':\n"))
      (let [results (concat (search-by-name SKILL_REGISTRY query)
                            (search-by-keyword SKILL_REGISTRY query))]
        (if (empty? results)
          (println "  No skills found.")
          (doseq [[_ skill] (take 10 results)]
            (print-skill skill)))))

    (and (>= (count args) 2) (= (first args) "trit"))
    (let [trit-str (second args)
          trit (Integer/parseInt trit-str)]
      (println (str "\n🔵 Skills with trit " trit-str ":\n"))
      (let [results (search-by-trit SKILL_REGISTRY trit)]
        (doseq [[_ skill] results]
          (print-skill skill))))

    (and (>= (count args) 2) (= (first args) "top-ie"))
    (let [count-str (second args)
          count (Integer/parseInt count-str)]
      (println (str "\n📈 Top " count-str " highest Information Energy skills:\n"))
      (let [results (take count (by-ie-score SKILL_REGISTRY))]
        (doseq [[_ skill] results]
          (print-skill skill))))

    :else
    (do
      (println "Usage: registry.bb [command]")
      (println "\nCommands:")
      (println "  list             List all 69 skills")
      (println "  stats            Show registry statistics")
      (println "  search <query>   Search by name or keyword")
      (println "  trit <-1|0|1>    Filter by trit")
      (println "  top-ie <count>   Show highest IE skills"))))

;; ============================================================================
;; MAIN
;; ============================================================================

(if (not-empty *command-line-args*)
  (handle-cli *command-line-args*)
  (do
    (show-registry-summary SKILL_REGISTRY)
    (println "\n💡 Tip: Run with 'list' to see all skills\n")))
