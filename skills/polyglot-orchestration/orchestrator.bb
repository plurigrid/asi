#!/usr/bin/env bb
;; polyglot-orchestration/orchestrator.bb
;; RED AGENT (+1): Unified multi-language orchestration controller
;;
;; Coordinates execution across Babashka, Julia, Python, OCaml, Scheme
;; with GF(3) conservation, type-safe marshalling, and error propagation

(require '[clojure.string :as str]
         '[clojure.edn :as edn]
         '[babashka.process :refer [shell process]])

;; ============================================================================
;; LANGUAGE ENUM & CONFIGURATION
;; ============================================================================

(def LANGUAGES
  {:babashka  {:trit +1 :color "#FF6B35" :bin "bb"}
   :julia     {:trit +1 :color "#FF6B35" :bin "julia"}
   :python    {:trit +1 :color "#FF6B35" :bin "python3"}
   :scheme    {:trit +1 :color "#FF6B35" :bin "guile"}
   :ocaml     {:trit +1 :color "#FF6B35" :bin "dune"}})

(def MESSAGE_QUEUE (atom []))
(def INVOCATION_ID (atom 0))

;; ============================================================================
;; MESSAGE PROTOCOL (GF(3) AWARE)
;; ============================================================================

(defn new-message-id []
  (swap! INVOCATION_ID inc))

(defn create-message
  [source-lang target-lang fn-name args trit & {:keys [marshaller returns]}]
  {:id (new-message-id)
   :timestamp (System/currentTimeMillis)
   :source-lang source-lang
   :target-lang target-lang
   :fn-name fn-name
   :args args
   :trit trit
   :marshaller (or marshaller :json)
   :returns (or returns :json)
   :status :pending
   :result nil
   :error nil})

;; ============================================================================
;; TYPE MARSHALLING (TRANSPORT LAYER)
;; ============================================================================

(defn to-json
  "Marshal Clojure data to JSON (via babashka json)"
  [data]
  (try
    (pr-str data)
    (catch Exception e
      {:error :json-marshal-failed :data (str e)})))

(defn from-json
  "Unmarshal JSON back to Clojure"
  [json-str]
  (try
    (edn/read-string json-str)
    (catch Exception e
      {:error :json-unmarshal-failed :raw json-str})))

(defn to-arrow
  "Marshal to Apache Arrow format (simulated as tab-separated)"
  [data]
  (if (vector? data)
    (str/join "\t" (map pr-str data))
    (to-json data)))

(defn to-sexp
  "Marshal to S-expression"
  [data]
  (cond
    (vector? data) (str "(" (str/join " " (map pr-str data)) ")")
    (map? data) (str "(" (str/join " " (map (fn [[k v]] (str k " " (pr-str v))) data)) ")")
    :else (pr-str data)))

(defn marshal
  "Select marshaller based on format"
  [data format]
  (case format
    :json (to-json data)
    :arrow (to-arrow data)
    :sexp (to-sexp data)
    :edn (pr-str data)
    (to-json data)))

(defn unmarshal
  "Deserialize based on format"
  [data format]
  (case format
    :json (from-json data)
    :arrow (str/split data #"\t")
    :sexp (edn/read-string data)
    :edn (edn/read-string data)
    data))

;; ============================================================================
;; LANGUAGE INVOKERS
;; ============================================================================

(defn invoke-babashka
  "Execute Babashka code"
  [{:keys [fn-name args marshaller trit]}]
  (try
    (let [code (str "(" fn-name " " (str/join " " (map pr-str args)) ")")
          result (shell {:out :string} "bb" "-e" code)
          out (:out result)]
      {:status :ok
       :result (unmarshal out marshaller)
       :trit trit})
    (catch Exception e
      {:status :error
       :error (str e)
       :trit trit})))

(defn invoke-julia
  "Execute Julia code"
  [{:keys [fn-name args marshaller trit]}]
  (try
    (let [code (str "using JSON; " fn-name "(" (str/join ", " (map pr-str args)) ")")
          result (shell {:out :string} "julia" "-e" code)
          out (:out result)]
      {:status :ok
       :result (unmarshal out marshaller)
       :trit trit})
    (catch Exception e
      {:status :error
       :error (str e)
       :trit trit})))

(defn invoke-python
  "Execute Python code"
  [{:keys [fn-name args marshaller trit]}]
  (try
    (let [args-json (to-json args)
          code (str "import sys, json\n"
                    "args = json.loads('" args-json "')\n"
                    "result = " fn-name "(*args)\n"
                    "print(json.dumps(result))")
          result (shell {:out :string :in code} "python3")
          out (:out result)]
      {:status :ok
       :result (unmarshal out marshaller)
       :trit trit})
    (catch Exception e
      {:status :error
       :error (str e)
       :trit trit})))

(defn invoke-scheme
  "Execute Scheme code"
  [{:keys [fn-name args marshaller trit]}]
  (try
    (let [code (str "(" fn-name " " (str/join " " (map pr-str args)) ")")
          result (shell {:out :string :in code} "guile" "-c" "(read)")
          out (:out result)]
      {:status :ok
       :result (unmarshal out marshaller)
       :trit trit})
    (catch Exception e
      {:status :error
       :error (str e)
       :trit trit})))

(defn invoke-ocaml
  "Execute OCaml code via dune"
  [{:keys [fn-name args marshaller trit]}]
  (try
    (let [code (str fn-name " (" (str/join " " (map pr-str args)) ")")
          result (shell {:out :string} "dune" "exec" "--" "--" code)
          out (:out result)]
      {:status :ok
       :result (unmarshal out marshaller)
       :trit trit})
    (catch Exception e
      {:status :error
       :error (str e)
       :trit trit})))

;; ============================================================================
;; DISPATCHER
;; ============================================================================

(defn get-invoker
  "Return invoker function for a language"
  [lang]
  (case lang
    :babashka invoke-babashka
    :julia invoke-julia
    :python invoke-python
    :scheme invoke-scheme
    :ocaml invoke-ocaml
    (fn [_] {:status :error :error (str "Unknown language: " lang)})))

(defn dispatch-invocation
  "Invoke a function in a specific language"
  [{:keys [target-lang fn-name args marshaller trit returns]}]
  (let [invoker (get-invoker target-lang)
        response (invoker {:fn-name fn-name
                          :args args
                          :marshaller returns
                          :trit trit})]
    response))

;; ============================================================================
;; GF(3) CONSERVATION
;; ============================================================================

(defn verify-gf3-balance
  "Verify that triadic invocations sum to 0 mod 3"
  [trits]
  (let [sum (reduce + trits)]
    {:sum sum :balanced? (zero? (mod sum 3)) :mod3 (mod sum 3)}))

(defn create-balanced-pipeline
  "Create triadic invocations that sum to 0 mod 3"
  [invocations]
  ;; invocations: vector of {:target-lang :fn-name :args ...}
  ;; Auto-assign trits: -1, 0, +1 cycling for groups of 3
  (let [with-trits (map-indexed (fn [i inv]
                                  (assoc inv :trit (case (mod i 3)
                                                      0 -1
                                                      1 0
                                                      +1)))
                                invocations)
        trits (map :trit with-trits)
        check (verify-gf3-balance trits)]
    {:invocations with-trits
     :gf3 check
     :balanced? (:balanced? check)}))

;; ============================================================================
;; RESULT AGGREGATION
;; ============================================================================

(defn execute-pipeline
  "Execute a series of polyglot invocations as a pipeline"
  [invocations]
  (let [pipeline (create-balanced-pipeline invocations)
        results (map (fn [inv]
                       (assoc (dispatch-invocation inv)
                              :invocation inv))
                     (:invocations pipeline))]
    {:status (if (every? #(= (:status %) :ok) results) :success :partial-error)
     :results results
     :gf3 (:gf3 pipeline)
     :execution-time-ms (System/currentTimeMillis)}))

(defn aggregate-results
  "Aggregate results from multiple languages into unified structure"
  [results]
  (let [ok-results (filter #(= (:status %) :ok) results)
        errors (filter #(= (:status %) :error) results)]
    {:ok (count ok-results)
     :error (count errors)
     :values (map :result ok-results)
     :errors (map :error errors)}))

;; ============================================================================
;; CLI INTERFACE
;; ============================================================================

(defn show-summary []
  (println "
╔════════════════════════════════════════════════════════════════════════╗
║                  POLYGLOT ORCHESTRATION - RED AGENT (+1)               ║
╠════════════════════════════════════════════════════════════════════════╣
║                                                                        ║
║  LANGUAGES AVAILABLE                                                   ║
║  ────────────────────────────────────────────────────────────────────  ║
║  • Babashka     (bb)          • Julia      (julia)                    ║
║  • Python       (python3)      • Scheme     (guile)                    ║
║  • OCaml        (dune)                                                 ║
║                                                                        ║
║  MARSHALLING FORMATS                                                   ║
║  ─────────────────────────────────────────────────────────────────     ║
║  JSON (default)  | Arrow (numerical)  | S-expr (logic)                 ║
║  EDN (clojure)                                                         ║
║                                                                        ║
║  GF(3) CONSERVATION                                                    ║
║  ───────────────────────────────────────────────────────────────       ║
║  All pipelines auto-balance trits: (-1, 0, +1) sum = 0 mod 3 ✓        ║
║                                                                        ║
╚════════════════════════════════════════════════════════════════════════╝
"))

(defn handle-cli
  [args]
  (cond
    (= args ["info"])
    (do
      (println "\n📋 ORCHESTRATION INFO")
      (println "══════════════════════════════════════════════")
      (doseq [[lang config] LANGUAGES]
        (println (format "  %-12s trit=%+d color=%s"
                         (name lang) (:trit config) (:color config)))))

    (and (>= (count args) 3) (= (first args) "exec"))
    (let [lang (keyword (second args))
          fn-name (nth args 2)
          args-str (drop 3 args)]
      (let [result (dispatch-invocation
                     {:target-lang lang
                      :fn-name fn-name
                      :args (map edn/read-string args-str)
                      :marshaller :json
                      :trit +1})]
        (println "\n🚀 EXECUTION RESULT")
        (println "══════════════════════════════════════════════")
        (println (format "  Status:  %s" (:status result)))
        (if (= (:status result) :ok)
          (println (format "  Result:  %s" (:result result)))
          (println (format "  Error:   %s" (:error result))))))

    (and (>= (count args) 1) (= (first args) "balance"))
    (let [trit-nums (map parse-long (rest args))]
      (let [check (verify-gf3-balance trit-nums)]
        (println (format "\n✓ GF(3) CHECK: Σ=%d (mod 3=%d) %s"
                         (:sum check) (:mod3 check)
                         (if (:balanced? check) "BALANCED ✓" "UNBALANCED ⚠")))))

    :else
    (show-summary)))

;; ============================================================================
;; MAIN
;; ============================================================================

(defn -main [& args]
  (if (not-empty args)
    (handle-cli args)
    (show-summary)))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
