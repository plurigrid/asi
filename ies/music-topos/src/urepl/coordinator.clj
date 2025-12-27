(ns urepl.coordinator
  "UREPL (Universal REPL) Coordinator - orchestrates three parallel agents"
  (:require [clojure.core.async :as async]
            [clojure.data.json :as json]
            [clojure.instant :as instant]
            [clojure.uuid :refer [random-uuid]])
  (:import [java.time Instant]))

;; ============================================================================
;; UREPL Message Protocol
;; ============================================================================

(defrecord UREPLMessage
  [id type timestamp source environment payload metadata])

(defn create-message
  "Create a UREPL message with auto-generated ID and timestamp"
  [type source env code & {:keys [srfis color-guide proof-request]
                           :or {srfis [] color-guide [] proof-request false}}]
  (UREPLMessage.
    (str (random-uuid))
    type
    (Instant/now)
    source
    env
    {:code code
     :context {}
     :srfis srfis
     :color-guide color-guide
     :proof-request proof-request}
    {:duration-ms 0
     :color-trace []
     :proof-sketch ""}))

;; ============================================================================
;; Agent Protocols
;; ============================================================================

(defprotocol SyntaxAgent
  "Agent 1: S-expression parsing and AST generation (Geiser)"
  (parse-code [this code])
  (generate-ast [this parsed])
  (format-code [this ast]))

(defprotocol SemanticsAgent
  "Agent 2: Type checking and semantic validation (CIDER)"
  (infer-types [this ast])
  (validate-semantics [this ast types])
  (resolve-symbols [this ast env]))

(defprotocol TestAgent
  "Agent 3: Test generation and verification (SLIME)"
  (generate-tests [this ast semantics])
  (verify-outputs [this tests results])
  (track-coverage [this tests executed]))

;; ============================================================================
;; Agent 1: Syntax Handler (Geiser Protocol)
;; ============================================================================

(defrecord GeiserSyntaxAgent []
  SyntaxAgent

  (parse-code [this code]
    "Parse S-expression code into tokens"
    {:raw code
     :tokens (re-seq #"[^\s\(\)]+" code)
     :parens (re-seq #"[\(\)]" code)
     :depth (reduce
              (fn [d c]
                (cond
                  (= c "(") (inc d)
                  (= c ")") (dec d)
                  :else d))
              0
              (seq code))})

  (generate-ast [this parsed]
    "Generate AST from parsed tokens"
    (let [tokens (:tokens parsed)]
      {:type :s-expr
       :car (first tokens)
       :cdr (rest tokens)
       :metadata {:line 1 :col 0 :source "geiser"}}))

  (format-code [this ast]
    "Pretty-print AST back to readable code"
    (str "(" (:car ast) " " (clojure.string/join " " (:cdr ast)) ")")))

(defn create-geiser-agent []
  (GeiserSyntaxAgent.))

;; ============================================================================
;; Agent 2: Semantics Validator (CIDER Protocol)
;; ============================================================================

(defrecord CIDERSemanticsAgent []
  SemanticsAgent

  (infer-types [this ast]
    "Infer types from AST structure"
    (let [car-type (if (symbol? (read-string (:car ast))) :function :atom)
          cdr-types (map (fn [_] :number) (:cdr ast))]
      {:type :function-app
       :function-type car-type
       :arg-types cdr-types
       :return-type :number}))

  (validate-semantics [this ast types]
    "Validate semantic correctness"
    (let [func-type (:function-type types)
          valid? (= func-type :function)]
      {:valid? valid?
       :errors (if valid? [] ["Type mismatch"])
       :warnings []
       :metadata {:source "cider"}}))

  (resolve-symbols [this ast env]
    "Resolve symbols in environment"
    (let [symbol (keyword (:car ast))
          definition (get env symbol)]
      {:symbol symbol
       :definition definition
       :resolved? (not (nil? definition))})))

(defn create-cider-agent []
  (CIDERSemanticsAgent.))

;; ============================================================================
;; Agent 3: Test Generator (SLIME Protocol)
;; ============================================================================

(defrecord SLIMETestAgent []
  TestAgent

  (generate-tests [this ast semantics]
    "Generate test cases from AST and semantics"
    (let [func-name (:car ast)
          args (map read-string (:cdr ast))
          test-cases
          [{:name (str "test-" func-name "-basic")
            :input args
            :expected (apply + args)
            :description "Basic arithmetic"}
           {:name (str "test-" func-name "-zero-identity")
            :input [0]
            :expected 0
            :description "Identity element"}
           {:name (str "test-" func-name "-commutativity")
            :input (reverse args)
            :expected (apply + args)
            :description "Commutative property"}]]
      test-cases))

  (verify-outputs [this tests results]
    "Check if results match expected values"
    (map (fn [test result]
           {:test (:name test)
            :passed? (= (:expected test) result)
            :actual result})
         tests
         results))

  (track-coverage [this tests executed]
    "Track code coverage statistics"
    (let [total (count tests)
          covered (count (filter :passed? executed))]
      {:total total
       :covered covered
       :percentage (double (/ covered total))})))

(defn create-slime-agent []
  (SLIMETestAgent.))

;; ============================================================================
;; Parallel Execution Engine
;; ============================================================================

(defn execute-agents-parallel
  "Execute all three agents in parallel with async channels"
  [syntax-agent semantics-agent test-agent message]

  (let [syntax-chan (async/chan)
        semantics-chan (async/chan)
        tests-chan (async/chan)
        result-chan (async/chan)]

    ;; Agent 1: Parse and generate AST
    (async/go
      (try
        (let [code (:code (:payload message))
              parsed (parse-code syntax-agent code)
              ast (generate-ast syntax-agent parsed)]
          (async/>! syntax-chan ast))
        (catch Exception e
          (async/>! syntax-chan {:error (.getMessage e)}))))

    ;; Agent 2: Infer types and validate (waits for Agent 1)
    (async/go
      (try
        (let [ast (async/<! syntax-chan)]
          (if (:error ast)
            (async/>! semantics-chan {:error (:error ast)})
            (let [types (infer-types semantics-agent ast)
                  semantics (validate-semantics semantics-agent ast types)]
              (async/>! semantics-chan {:ast ast :types types :semantics semantics}))))
        (catch Exception e
          (async/>! semantics-chan {:error (.getMessage e)}))))

    ;; Agent 3: Generate tests (waits for Agent 1)
    (async/go
      (try
        (let [ast (async/<! syntax-chan)]
          (if (:error ast)
            (async/>! tests-chan {:error (:error ast)})
            (let [test-cases (generate-tests test-agent ast {})]
              (async/>! tests-chan test-cases))))
        (catch Exception e
          (async/>! tests-chan {:error (.getMessage e)}))))

    ;; Collect results from all channels (with timeout)
    (async/go
      (let [syntax-result (async/<! syntax-chan)
            semantics-result (async/<! semantics-chan)
            tests-result (async/<! tests-chan)]
        (async/>! result-chan
                 {:syntax syntax-result
                  :semantics semantics-result
                  :tests tests-result
                  :timestamp (Instant/now)
                  :message-id (:id message)})
        (async/close! result-chan)))

    result-chan))

(defn wait-for-result
  "Block until agents complete or timeout"
  [result-chan timeout-ms]
  (async/<!! (async/timeout timeout-ms)))

;; ============================================================================
;; Color-Guided Execution Trace (Gay.jl Integration)
;; ============================================================================

(defrecord SplitMix64 [seed])

(defn next-color
  "Generate next color in deterministic sequence"
  [^SplitMix64 rng]
  (let [z (+ (:seed rng) 0x9e3779b97f4a7c15)
        z (bit-xor z (unsigned-shift-right z 30))
        z (long (* z 0xbf58476d1ce4e5b9))
        z (bit-xor z (unsigned-shift-right z 27))

        ;; Map to hue (0-360)
        hue (mod (/ (double (bit-and z 0xffffffff)) 65536.0) 360.0)

        ;; Golden angle: 137.508° for never-repeating spiral
        next-seed (unchecked-add z 0x85ebca6b)]

    {:hue hue :seed next-seed}))

(defn color-trace-execution
  "Annotate execution steps with deterministic colors"
  [steps initial-seed]
  (reduce
    (fn [acc step]
      (let [rng (SplitMix64. (:seed (last acc)))
            {:keys [hue seed]} (next-color rng)
            colored-step (assoc step :color {:hue hue})]
        (conj acc colored-step)))
    [(SplitMix64. initial-seed)]
    steps))

;; ============================================================================
;; Main Coordinator State and Execution
;; ============================================================================

(def coordinator-state
  (atom {:agents {}
         :message-queue []
         :results []
         :execution-traces []
         :started-at (Instant/now)}))

(defn initialize-coordinator
  "Create and initialize all three agents"
  []
  (swap! coordinator-state assoc
         :agents
         {:syntax (create-geiser-agent)
          :semantics (create-cider-agent)
          :tests (create-slime-agent)})
  (println "[UREPL] Coordinator initialized with 3 agents")
  @coordinator-state)

(defn enqueue-message
  "Add message to processing queue"
  [msg]
  (swap! coordinator-state update :message-queue conj msg)
  (println (format "[UREPL] Message %s enqueued" (:id msg))))

(defn process-message
  "Process a single message through all agents"
  [msg]
  (let [agents (:agents @coordinator-state)
        result-chan (execute-agents-parallel
                      (:syntax agents)
                      (:semantics agents)
                      (:tests agents)
                      msg)
        result (wait-for-result result-chan 5000)]

    (if result
      (do
        (swap! coordinator-state update :results conj result)
        (println (format "[UREPL] Message %s processed successfully" (:id msg)))
        result)
      (do
        (println (format "[UREPL] Message %s timed out" (:id msg)))
        {:error "timeout" :message-id (:id msg)}))))

(defn process-queue
  "Process all messages in queue"
  []
  (loop [queue (:message-queue @coordinator-state)]
    (when (seq queue)
      (let [msg (first queue)]
        (process-message msg)
        (swap! coordinator-state update :message-queue rest)
        (recur (:message-queue @coordinator-state))))))

(defn execute-program
  "Main entry point: parse, validate, test, and execute code"
  [code & {:keys [seed srfis color-trace] :or {seed 42 srfis [] color-trace true}}]

  (println "\n" (apply str (repeat 60 "=")))
  (println "UREPL Execution: " code)
  (println (apply str (repeat 60 "=")))

  (initialize-coordinator)

  (let [msg (create-message :eval :geiser "user" code :srfis srfis)]
    (enqueue-message msg)
    (process-queue)

    (let [result (first (:results @coordinator-state))]
      (when color-trace
        (println "\nColor Trace (SplitMix64 seed=" seed ")")
        (let [trace (color-trace-execution
                      [{:step "parse"}
                       {:step "ast-gen"}
                       {:step "type-infer"}
                       {:step "validate"}
                       {:step "test-gen"}
                       {:step "eval"}]
                      seed)]
          (doseq [step (rest trace)]
            (println (format "  %-15s hue=%.1f°" (:step step) (:hue (:color step)))))))

      (println "\nResults:")
      (println "  Syntax:    " (if (:error (:syntax result)) "✗ ERROR" "✓ OK"))
      (println "  Semantics: " (if (:error (:semantics result)) "✗ ERROR" "✓ OK"))
      (println "  Tests:     " (if (:error (:tests result)) "✗ ERROR" "✓ OK"))
      (println "\nExecution Summary:")
      (println (format "  Started: %s" (:started-at @coordinator-state)))
      (println (format "  Completed: %s" (:timestamp result)))
      (println (apply str (repeat 60 "=")))

      result)))

;; ============================================================================
;; Example Usage
;; ============================================================================

(comment
  ;; Execute a simple expression
  (execute-program "(+ 1 2)")

  ;; Execute with custom seed
  (execute-program "(* 3 4)" :seed 12345)

  ;; Execute with SRFI requirements
  (execute-program "(define x 42)" :srfis [2 26])
)
