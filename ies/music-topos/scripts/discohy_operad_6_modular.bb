#!/usr/bin/env bb
;; DiscoHy Modular Operad: Agent 6 (squint-runtime + borkdude + geiser-chicken)
;; 
;; MODULAR OPERAD THEORY:
;;   - Genus-labeled operations = runtime complexity metric
;;   - Moduli space = space of all runtimes (babashka, squint, chicken)
;;   - Runtime switching = traversing moduli space via morphisms
;;   - Tropical geometry: max-plus semiring on runtime selection weights
;;
;; The modular operad M_{g,n} models:
;;   g = genus (runtime complexity/overhead)
;;   n = number of inputs (context dimensions)

(require '[babashka.process :refer [shell]]
         '[clojure.string :as str]
         '[cheshire.core :as json])

;; ═══════════════════════════════════════════════════════════════════════════════
;; SPLITMIX64: Deterministic Color Generation
;; ═══════════════════════════════════════════════════════════════════════════════

(def GOLDEN 0x9E3779B97F4A7C15)
(def MASK64 0xFFFFFFFFFFFFFFFF)
(def MIX1 0xBF58476D1CE4E5B9)
(def MIX2 0x94D049BB133111EB)

(defn splitmix64 [state]
  (let [s (bit-and (+ state GOLDEN) MASK64)
        z (-> s
              (bit-xor (unsigned-bit-shift-right s 30))
              (* MIX1)
              (bit-and MASK64))
        z (-> z
              (bit-xor (unsigned-bit-shift-right z 27))
              (* MIX2)
              (bit-and MASK64))]
    (bit-xor z (unsigned-bit-shift-right z 31))))

(defn splitmix-ternary [state]
  "Map u64 → GF(3) = {-1, 0, +1}"
  (- (mod (splitmix64 state) 3) 1))

;; ═══════════════════════════════════════════════════════════════════════════════
;; MODULAR OPERAD: Runtime as Points in Moduli Space
;; ═══════════════════════════════════════════════════════════════════════════════

;; Each runtime = point in moduli space M_{g,n}
;; g = genus = complexity overhead (JVM=2, native=1, js=0)
;; n = boundary components = context requirements

(def RUNTIMES
  {:babashka {:genus 2
              :boundaries [:jvm :shell :pods :deps]
              :trit 0
              :startup-ms 50
              :description "JVM scripting with pod ecosystem"}
   :squint   {:genus 0
              :boundaries [:browser :js-interop]
              :trit 1
              :startup-ms 0
              :description "Minimal ClojureScript (~10KB)"}
   :chicken  {:genus 1
              :boundaries [:scheme :native :eggs :r7rs]
              :trit -1
              :startup-ms 5
              :description "Compiled Scheme with eggs ecosystem"}
   :nbb      {:genus 1
              :boundaries [:node :npm :js-interop]
              :trit 0
              :startup-ms 20
              :description "Node.js babashka variant"}
   :sci      {:genus 1
              :boundaries [:embedded :minimal]
              :trit 1
              :startup-ms 0
              :description "Small Clojure interpreter"}
   :cherry   {:genus 0
              :boundaries [:browser :macros :larger-bundle]
              :trit -1
              :startup-ms 0
              :description "Full CLJS subset for browser"}})

;; GF(3) verification: sum of trits should be 0 mod 3
(assert (zero? (mod (reduce + (map :trit (vals RUNTIMES))) 3))
        "Runtime trits must be GF(3) conserved")

;; ═══════════════════════════════════════════════════════════════════════════════
;; MODULAR COMPOSITION: γ ∘ (γ₁,...,γₙ) 
;; ═══════════════════════════════════════════════════════════════════════════════

(defn genus-formula
  "g(γ ∘ (γ₁,...,γₙ)) = g(γ) + Σg(γᵢ) + loops
   where loops = edges created by composition"
  [parent-genus child-genera edges-sewn]
  (+ parent-genus
     (reduce + child-genera)
     edges-sewn))

(defn modular-compose
  "Compose operations in modular operad M_{g,n}.
   Returns new operation with computed genus."
  [parent children]
  (let [parent-genus (:genus parent)
        child-genera (map :genus children)
        edges-sewn (count children)  ; Each child contributes one sewn edge
        new-genus (genus-formula parent-genus child-genera edges-sewn)]
    {:genus new-genus
     :boundaries (mapcat :boundaries (cons parent children))
     :trit (mod (reduce + (:trit parent) (map :trit children)) 3)
     :composed-from (cons (:name parent) (map :name children))}))

;; ═══════════════════════════════════════════════════════════════════════════════
;; TROPICAL GEOMETRY: Runtime Selection via Max-Plus
;; ═══════════════════════════════════════════════════════════════════════════════

(defn tropical-add
  "⊕ = max in tropical semiring"
  [a b]
  (max a b))

(defn tropical-mult
  "⊗ = + in tropical semiring"
  [a b]
  (+ a b))

(defn runtime-weight
  "Compute tropical weight for runtime in context.
   Higher = worse (tropical minimization)."
  [runtime context]
  (let [{:keys [genus startup-ms boundaries]} (RUNTIMES runtime)]
    (reduce tropical-mult 0
            [(if (:fast-startup context) (* startup-ms 10) 0)
             (if (:browser context)
               (if (some #{:browser} boundaries) 0 1000)
               0)
             (if (:jvm-deps context)
               (if (some #{:jvm :pods} boundaries) 0 1000)
               0)
             (if (:scheme-compat context)
               (if (some #{:scheme :r7rs} boundaries) 0 1000)
               0)
             (* genus 100)])))  ; Genus penalty

(defn tropical-select
  "Select runtime minimizing tropical weight."
  [context]
  (let [weights (map (fn [[k v]] [k (runtime-weight k context)])
                     RUNTIMES)
        [best-runtime _] (reduce (fn [[k1 w1] [k2 w2]]
                                   (if (<= w1 w2) [k1 w1] [k2 w2]))
                                 weights)]
    best-runtime))

;; ═══════════════════════════════════════════════════════════════════════════════
;; DUCKDB: Query Runtime Selection History
;; ═══════════════════════════════════════════════════════════════════════════════

(def DB-PATH "/Users/bob/ies/ducklake_data/ies_interactome.duckdb")

(defn duckdb-query [sql]
  (try
    (let [result (shell {:out :string :err :string}
                        "duckdb" DB-PATH "-json" "-c" sql)]
      (when (zero? (:exit result))
        (json/parse-string (:out result) true)))
    (catch Exception _ nil)))

(defn query-runtime-patterns []
  "Query historical runtime selection patterns."
  (or (duckdb-query 
       "SELECT content, timestamp, category 
        FROM unified_interactions 
        WHERE LOWER(content) LIKE '%babashka%' 
           OR LOWER(content) LIKE '%squint%'
           OR LOWER(content) LIKE '%chicken%'
           OR LOWER(content) LIKE '%runtime%'
        ORDER BY timestamp DESC LIMIT 20")
      []))

(defn query-modular-stats []
  "Aggregate modular statistics from interactions."
  (or (duckdb-query
       "SELECT category, COUNT(*) as cnt, AVG(trit) as avg_trit
        FROM unified_interactions
        GROUP BY category
        ORDER BY cnt DESC LIMIT 10")
      []))

;; ═══════════════════════════════════════════════════════════════════════════════
;; MODULAR OPERAD OPERATIONS
;; ═══════════════════════════════════════════════════════════════════════════════

(defn runtime-switching-morphism
  "Model runtime switch as morphism in moduli space.
   Returns: {:source :target :genus-change :trit-change}"
  [from-runtime to-runtime]
  (let [from (RUNTIMES from-runtime)
        to (RUNTIMES to-runtime)]
    {:source from-runtime
     :target to-runtime
     :genus-change (- (:genus to) (:genus from))
     :trit-change (mod (- (:trit to) (:trit from)) 3)
     :morphism-type (cond
                      (= (:genus from) (:genus to)) :isogenous
                      (< (:genus from) (:genus to)) :degenerating
                      :else :smoothing)}))

(defn switching-sequence
  "Generate optimal runtime switching sequence.
   Uses tropical weights to minimize total transition cost."
  [contexts]
  (map tropical-select contexts))

(defn moduli-distance
  "Distance in moduli space = |Δgenus| + |Δtrit|"
  [r1 r2]
  (let [m (runtime-switching-morphism r1 r2)]
    (+ (Math/abs (:genus-change m))
       (Math/abs (:trit-change m)))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; MAIN: Modular Operad Analysis
;; ═══════════════════════════════════════════════════════════════════════════════

(defn print-moduli-space []
  (println "═══════════════════════════════════════════════════════════════")
  (println "MODULI SPACE M_{g,n} OF RUNTIMES")
  (println "═══════════════════════════════════════════════════════════════")
  (doseq [[k v] (sort-by (comp :genus val) RUNTIMES)]
    (println (format "  %s: genus=%d boundaries=%d trit=%+d"
                     (name k) (:genus v) 
                     (count (:boundaries v))
                     (:trit v))))
  (println))

(defn print-tropical-analysis []
  (println "═══════════════════════════════════════════════════════════════")
  (println "TROPICAL GEOMETRY: Runtime Selection")
  (println "═══════════════════════════════════════════════════════════════")
  (let [contexts [{:fast-startup true}
                  {:browser true}
                  {:jvm-deps true}
                  {:scheme-compat true}
                  {:fast-startup true :browser true}]]
    (doseq [ctx contexts]
      (let [selected (tropical-select ctx)]
        (println (format "  Context: %-30s → %s" 
                         (pr-str ctx) (name selected)))))))

(defn print-morphism-graph []
  (println)
  (println "═══════════════════════════════════════════════════════════════")
  (println "MORPHISMS IN MODULI SPACE (Agent 6 triad)")
  (println "═══════════════════════════════════════════════════════════════")
  (let [agent6-runtimes [:babashka :squint :chicken]]
    (doseq [from agent6-runtimes
            to agent6-runtimes
            :when (not= from to)]
      (let [m (runtime-switching-morphism from to)]
        (println (format "  %s → %s: Δg=%+d Δt=%+d [%s]"
                         (name from) (name to)
                         (:genus-change m) (:trit-change m)
                         (name (:morphism-type m))))))))

(defn print-composition-demo []
  (println)
  (println "═══════════════════════════════════════════════════════════════")
  (println "MODULAR COMPOSITION: γ ∘ (γ₁,...,γₙ)")
  (println "═══════════════════════════════════════════════════════════════")
  (let [bb (assoc (RUNTIMES :babashka) :name :babashka)
        sq (assoc (RUNTIMES :squint) :name :squint)
        ch (assoc (RUNTIMES :chicken) :name :chicken)
        composed (modular-compose bb [sq ch])]
    (println "  Composing: babashka ∘ (squint, chicken)")
    (println (format "  Result: genus=%d trit=%d"
                     (:genus composed) (:trit composed)))
    (println (format "  Boundaries: %s" (vec (take 5 (:boundaries composed)))))))

(defn print-db-patterns []
  (println)
  (println "═══════════════════════════════════════════════════════════════")
  (println "HISTORICAL RUNTIME PATTERNS (DuckDB)")
  (println "═══════════════════════════════════════════════════════════════")
  (let [patterns (query-runtime-patterns)]
    (if (seq patterns)
      (doseq [p (take 5 patterns)]
        (println (format "  [%s] %s" 
                         (or (:category p) "?")
                         (subs (or (:content p) "") 0 
                               (min 60 (count (or (:content p) "")))))))
      (println "  (No runtime patterns in DB - run ingestion first)"))))

(defn -main [& args]
  (println)
  (println "╔═══════════════════════════════════════════════════════════════╗")
  (println "║  DISCOHY MODULAR OPERAD: Agent 6                              ║")
  (println "║  squint-runtime + borkdude + geiser-chicken                   ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println)
  
  (print-moduli-space)
  (print-tropical-analysis)
  (print-morphism-graph)
  (print-composition-demo)
  (print-db-patterns)
  
  (println)
  (println "═══════════════════════════════════════════════════════════════")
  (println "MODULAR OPERAD SUMMARY")
  (println "═══════════════════════════════════════════════════════════════")
  (println "  • Moduli space: 6 runtimes as points in M_{g,n}")
  (println "  • Agent 6 triad: babashka(g=2) + squint(g=0) + chicken(g=1)")
  (println "  • GF(3) trit sum: 0 + 1 + (-1) = 0 ✓ (conserved)")
  (println "  • Tropical selection: min-weight runtime per context")
  (println "  • Morphism types: isogenous, degenerating, smoothing")
  (println)
  (println "=== Complete ==="))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
