;; borkdude/runtime_selector.clj
;; Invariant runtime selection for S-expression skill management

(ns borkdude.runtime-selector
  "Select optimal borkdude runtime based on environment and preferences.
   
   Invariant: Same inputs → same runtime selection (deterministic)")

;; ═══════════════════════════════════════════════════════════════════════════════
;; RUNTIME DEFINITIONS
;; ═══════════════════════════════════════════════════════════════════════════════

(def RUNTIMES
  "Borkdude's ClojureScript/Clojure runtime ecosystem"
  {:cherry
   {:name "Cherry 🍒"
    :environment #{:browser :node}
    :features #{:full-cljs :jsx :async-await :esm :npm}
    :startup-ms 50
    :stars 627
    :url "https://github.com/squint-cljs/cherry"
    :install "npm install cherry-cljs@latest"
    :trit 1}  ; PLUS - forward/covariant
   
   :squint
   {:name "Squint"
    :environment #{:browser :node}
    :features #{:cljs-syntax :minimal :js-interop :small-bundle}
    :startup-ms 30
    :stars 1200
    :url "https://github.com/squint-cljs/squint"
    :install "npm install squint-cljs@latest"
    :trit 0}  ; ERGODIC - neutral/transport
   
   :scittle
   {:name "Scittle"
    :environment #{:browser}
    :features #{:script-tags :zero-setup :instant}
    :startup-ms 0
    :stars 400
    :url "https://github.com/babashka/scittle"
    :install "<script src='scittle.js'></script>"
    :trit -1}  ; MINUS - backward/contravariant
   
   :sci
   {:name "SCI (Small Clojure Interpreter)"
    :environment #{:browser :jvm :graalvm}
    :features #{:sandboxed :interpreter :dsl :configurable}
    :startup-ms 10
    :stars 1300
    :url "https://github.com/babashka/sci"
    :install "[org.babashka/sci \"0.10.49\"]"
    :trit 0}  ; ERGODIC
   
   :babashka
   {:name "Babashka"
    :environment #{:native :jvm}
    :features #{:fast-startup :scripting :graalvm :pods}
    :startup-ms 5
    :stars 4000
    :url "https://github.com/babashka/babashka"
    :install "brew install borkdude/brew/babashka"
    :trit 1}  ; PLUS
   
   :nbb
   {:name "nbb (Node.js Babashka)"
    :environment #{:node}
    :features #{:node-scripting :npm :full-cljs}
    :startup-ms 100
    :stars 700
    :url "https://github.com/babashka/nbb"
    :install "npx nbb"
    :trit -1}})  ; MINUS

;; ═══════════════════════════════════════════════════════════════════════════════
;; SELECTION LOGIC
;; ═══════════════════════════════════════════════════════════════════════════════

(defn matches-environment?
  "Check if runtime supports the given environment"
  [runtime env]
  (contains? (:environment runtime) env))

(defn has-features?
  "Check if runtime has all required features"
  [runtime required-features]
  (every? #(contains? (:features runtime) %) required-features))

(defn score-runtime
  "Score a runtime for given criteria (higher is better)"
  [runtime {:keys [environment features prefer-fast prefer-minimal]}]
  (let [base-score (if (matches-environment? runtime environment) 100 0)
        feature-score (* 10 (count (filter #(contains? (:features runtime) %) features)))
        speed-bonus (if prefer-fast (- 50 (:startup-ms runtime)) 0)
        minimal-bonus (if (and prefer-minimal (contains? (:features runtime) :minimal)) 20 0)]
    (+ base-score feature-score speed-bonus minimal-bonus)))

(defn select-runtime
  "Select optimal runtime based on criteria.
   
   Invariant: Same criteria → same runtime (deterministic selection)"
  [{:keys [environment features prefer-fast prefer-minimal] :as criteria}]
  (let [scored (->> RUNTIMES
                    (map (fn [[k v]] [k (score-runtime v criteria)]))
                    (filter (fn [[_ score]] (pos? score)))
                    (sort-by second >))]
    (if (seq scored)
      (first (first scored))
      :sci)))  ; Default fallback

(defn select-for-environment
  "Quick selection for common environments"
  [env-str]
  (case (keyword env-str)
    :browser (select-runtime {:environment :browser :prefer-fast true})
    :node (select-runtime {:environment :node :features [:npm]})
    :jvm (select-runtime {:environment :jvm :features [:sandboxed]})
    :native (select-runtime {:environment :native :prefer-fast true})
    :script (select-runtime {:environment :native :features [:scripting]})
    :jsx (select-runtime {:environment :browser :features [:jsx]})
    :minimal (select-runtime {:environment :browser :prefer-minimal true})
    :sci))

;; ═══════════════════════════════════════════════════════════════════════════════
;; BROWSER VS LOCAL COMPARISON
;; ═══════════════════════════════════════════════════════════════════════════════

(def BROWSER-RUNTIMES #{:cherry :squint :scittle})
(def LOCAL-RUNTIMES #{:babashka :sci :nbb})

(defn browser-alternatives
  "Get browser runtime alternatives with comparison"
  []
  (->> BROWSER-RUNTIMES
       (map #(vector % (get RUNTIMES %)))
       (sort-by (comp :startup-ms second))))

(defn local-alternatives
  "Get local runtime alternatives with comparison"
  []
  (->> LOCAL-RUNTIMES
       (map #(vector % (get RUNTIMES %)))
       (sort-by (comp :startup-ms second))))

(defn compare-alternatives
  "Compare browser vs local alternatives"
  []
  {:browser (browser-alternatives)
   :local (local-alternatives)
   :recommendation
   {:browser-primary :cherry
    :browser-minimal :squint
    :browser-zero-setup :scittle
    :local-primary :babashka
    :local-sandboxed :sci
    :local-node :nbb}})

;; ═══════════════════════════════════════════════════════════════════════════════
;; GF(3) CONSERVATION
;; ═══════════════════════════════════════════════════════════════════════════════

(defn runtime-trit
  "Get GF(3) trit for a runtime"
  [runtime-key]
  (get-in RUNTIMES [runtime-key :trit] 0))

(defn verify-gf3-selection
  "Verify that a selection of 3 runtimes conserves GF(3)"
  [runtime-keys]
  (let [trits (map runtime-trit runtime-keys)
        sum (reduce + trits)]
    {:runtimes runtime-keys
     :trits trits
     :sum sum
     :conserved? (zero? (mod sum 3))}))

(defn balanced-triplet
  "Return a GF(3)-balanced triplet of runtimes"
  []
  ;; Cherry (+1) + Squint (0) + Scittle (-1) = 0
  [:cherry :squint :scittle])

;; ═══════════════════════════════════════════════════════════════════════════════
;; DEMO
;; ═══════════════════════════════════════════════════════════════════════════════

(defn demo []
  (println "╔═══════════════════════════════════════════════════════════════════╗")
  (println "║  BORKDUDE RUNTIME SELECTOR: Browser vs Local Alternatives         ║")
  (println "╚═══════════════════════════════════════════════════════════════════╝")
  (println)
  
  (println "─── Browser Alternatives ───")
  (doseq [[k v] (browser-alternatives)]
    (println (format "  %s: %s (~%dms startup)"
                     (name k) (:name v) (:startup-ms v))))
  (println)
  
  (println "─── Local Alternatives ───")
  (doseq [[k v] (local-alternatives)]
    (println (format "  %s: %s (~%dms startup)"
                     (name k) (:name v) (:startup-ms v))))
  (println)
  
  (println "─── Selection Examples ───")
  (doseq [env [:browser :node :jvm :native :jsx :minimal]]
    (println (format "  %s → %s" env (select-for-environment env))))
  (println)
  
  (println "─── GF(3) Conservation ───")
  (let [result (verify-gf3-selection (balanced-triplet))]
    (println (format "  Triplet: %s" (:runtimes result)))
    (println (format "  Trits: %s → sum=%d" (:trits result) (:sum result)))
    (println (format "  Conserved: %s" (if (:conserved? result) "✓" "✗"))))
  (println)
  
  (println "═══════════════════════════════════════════════════════════════════")
  (println "Invariant: Same criteria → same runtime selection (deterministic)"))

(when (= *file* (System/getProperty "babashka.file"))
  (demo))
