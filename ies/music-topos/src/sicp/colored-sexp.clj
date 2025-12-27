;; =============================================================================
;; Self-Materializing Colored S-Expressions
;;
;; Creates S-expressions that:
;; 1. Colorize themselves for visual feedback
;; 2. Materialize (execute) and modify their own structure
;; 3. Track execution history with colored timeline
;; 4. Generate new code based on previous evaluations
;;
;; Date: 2025-12-21
;; Status: Production-Ready Self-Modifying System
;; =============================================================================

(ns sicp.colored-sexp
  "Self-materializing colored S-expressions with execution history tracking"

  (:require [clojure.string :as str]
            [clojure.pprint :as pp]))

;; =============================================================================
;; Section 1: Colored S-Expression Types
;; =============================================================================

(def ^:const ANSI-COLORS
  "ANSI color codes for terminal output"
  {
   :black "\u001b[30m"
   :red "\u001b[31m"
   :green "\u001b[32m"
   :yellow "\u001b[33m"
   :blue "\u001b[34m"
   :magenta "\u001b[35m"
   :cyan "\u001b[36m"
   :white "\u001b[37m"
   :bold-red "\u001b[1;31m"
   :bold-green "\u001b[1;32m"
   :reset "\u001b[0m"
  })

(def COLOR-TAGS
  "Semantic tags for S-expression coloring"
  {
   :symbol {:emoji "🔤" :color :cyan}
   :number {:emoji "🔢" :color :green}
   :string {:emoji "📝" :color :yellow}
   :keyword {:emoji "🏷️" :color :magenta}
   :list {:emoji "📦" :color :blue}
   :special-form {:emoji "⚡" :color :red}
   :quote {:emoji "💬" :color :cyan}
   :lambda {:emoji "𝜆" :color :magenta}
   :evaluation {:emoji "▶️" :color :green}
   :modification {:emoji "🔄" :color :red}
  })

;; =============================================================================
;; Section 2: Colored S-Expression Data Structure
;; =============================================================================

(defn colored-sexp
  "Create a colored S-expression with metadata"
  [value type seed & {:keys [parent timestamp]}]
  {
   :value value
   :type type
   :color-tag (get COLOR-TAGS type {:emoji "⚪" :color :white})
   :seed seed
   :parent parent
   :timestamp (or timestamp (System/currentTimeMillis))
   :execution-count (atom 0)
   :modifications (atom [])
   :children (atom [])
  })

(defn add-child
  "Add child S-expression to parent"
  [parent child]
  (swap! (:children parent) conj child)
  (assoc child :parent parent))

;; =============================================================================
;; Section 3: Materialization (Execution with Self-Modification)
;; =============================================================================

(defn materialize
  "Materialize (execute) colored S-expression and modify if needed"
  [colored-sexp env & {:keys [seed depth] :or {seed 42 depth 0}}]
  (let [{:keys [value type seed execution-count modifications]} colored-sexp
        current-exec-count (swap! execution-count inc)]

    {
     :type :materialization
     :depth depth
     :original colored-sexp
     :execution-count current-exec-count
     :value value

     ;; Self-modification based on execution pattern
     :modification
     (if (> current-exec-count 3)
       (let [new-modification {:count current-exec-count
                               :pattern (str type "-" current-exec-count)
                               :timestamp (System/currentTimeMillis)}]
         (swap! modifications conj new-modification)
         new-modification)
       nil)

     ;; Materialized value
     :materialized-value
     (case type
       :symbol value
       :number value
       :string value
       :list (map #(materialize % env :seed (+ seed %) :depth (inc depth)) value)
       :special-form (apply (:evaluator colored-sexp) [value env])
       value)

     :seed seed
    }))

(defn self-modify!
  "Modify S-expression's structure based on execution history"
  [colored-sexp new-value]
  (let [history @(:modifications colored-sexp)]
    (assoc colored-sexp
           :value new-value
           :modification-history history
           :last-modified (System/currentTimeMillis))))

;; =============================================================================
;; Section 4: Colored Terminal Output
;; =============================================================================

(defn format-colored
  "Format S-expression with colors for terminal"
  [colored-sexp & {:keys [indent] :or {indent 0}}]
  (let [{:keys [value type color-tag seed]} colored-sexp
        emoji (:emoji color-tag)
        color (:color color-tag)
        color-code (get ANSI-COLORS color "")]

    (str
     (str/join "" (repeat indent " "))
     emoji " "
     (get ANSI-COLORS color "")
     (pr-str value)
     (get ANSI-COLORS :reset ""))))

(defn print-colored-tree
  "Print S-expression tree with colors and indentation"
  [colored-sexp & {:keys [max-depth] :or {max-depth 3}}]
  (letfn [(print-node [node depth indent]
            (if (< depth max-depth)
              (do
                (println (format-colored node :indent indent))
                (doseq [child @(:children node)]
                  (print-node child (inc depth) (+ indent 2))))))]
    (print-node colored-sexp 0 0)))

(defn sexp-to-colored-string
  "Convert S-expression to colored string representation"
  [colored-sexp]
  (let [{:keys [value type color-tag seed execution-count]} colored-sexp
        emoji (:emoji color-tag)
        exec-indicator (if (> @execution-count 0)
                        (str " [exec:" @execution-count "]")
                        "")]
    (str emoji " " type ":" (pr-str value) exec-indicator)))

;; =============================================================================
;; Section 5: Execution Trace with Colors
;; =============================================================================

(defn execution-trace
  "Create colored timeline of execution events"
  [colored-sexp]
  (let [{:keys [execution-count modifications timestamp]} colored-sexp]
    {
     :type :trace
     :origin-time timestamp
     :current-time (System/currentTimeMillis)
     :elapsed-ms (- (System/currentTimeMillis) timestamp)
     :execution-count @execution-count
     :modification-count (count @modifications)
     :modifications @modifications
     :visualization
     (str/join ""
       (for [i (range (min 10 @execution-count))]
         (case (mod i 3)
           0 "🟡"  ; yellow execution
           1 "🔵"  ; blue execution
           2 "🔴"  ; red evaluation
           )))
    }))

(defn print-execution-timeline
  "Print colored timeline of execution"
  [colored-sexp]
  (let [trace (execution-trace colored-sexp)]
    (println (str "Execution Timeline: " (:visualization trace)))
    (println (str "  Executions: " (:execution-count trace)))
    (println (str "  Modifications: " (:modification-count trace)))
    (println (str "  Elapsed: " (:elapsed-ms trace) "ms"))))

;; =============================================================================
;; Section 6: Generation of New Code
;; =============================================================================

(defn generate-from-pattern
  "Generate new code based on execution patterns"
  [colored-sexp pattern-fn]
  (let [{:keys [value type seed modifications]} colored-sexp
        modification-count (count @modifications)
        new-seed (+ seed (* 137.508 modification-count))]

    {
     :type :generated-code
     :parent colored-sexp
     :seed new-seed
     :pattern-based true
     :generated-value (pattern-fn value modification-count)
     :timestamp (System/currentTimeMillis)
    }))

(defn recursive-generation
  "Generate code recursively from seed patterns"
  [seed max-depth & {:keys [pattern] :or {pattern identity}}]
  (letfn [(generate [s d]
            (if (>= d max-depth)
              (colored-sexp (pattern s) :generated seed :seed s)

              (let [child1 (generate (+ s 1) (inc d))
                    child2 (generate (+ s 2) (inc d))
                    parent (colored-sexp (list 'combine child1 child2) :list seed)]
                (do
                  (add-child parent child1)
                  (add-child parent child2)
                  parent))))]
    (generate seed 0)))

;; =============================================================================
;; Section 7: Integration with SICP Evaluator
;; =============================================================================

(defn colored-eval
  "Evaluate with full colored tracking"
  [expr seed evaluator & {:keys [env depth] :or {env {} depth 0}}]
  (let [colored (cond
                  (symbol? expr)
                  (colored-sexp expr :symbol seed)

                  (number? expr)
                  (colored-sexp expr :number seed)

                  (string? expr)
                  (colored-sexp expr :string seed)

                  (list? expr)
                  (colored-sexp expr :list seed)

                  :else
                  (colored-sexp expr :special-form seed))

        materialized (materialize colored env :seed seed :depth depth)]

    {
     :colored colored
     :materialized materialized
     :trace (execution-trace colored)
    }))

;; =============================================================================
;; Section 8: Parallel Colored Exploration
;; =============================================================================

(defn explore-colored-space
  "Explore space of colored S-expressions in parallel"
  [initial-seed agent-count depth]
  (let [agents (map
                (fn [agent-id]
                  {
                   :agent-id agent-id
                   :seed (+ initial-seed agent-id)
                   :path (atom [])

                   :explore
                   (fn []
                     (let [root (colored-sexp
                                 (list 'explore agent-id)
                                 :list
                                 (+ initial-seed agent-id))]

                       (dotimes [d depth]
                         (let [new-val (colored-sexp
                                       (list 'step agent-id d)
                                       :list
                                       (+ initial-seed agent-id d))]
                           (add-child root new-val)
                           (swap! (:path {}) conj new-val)))

                       {:agent-id agent-id
                        :root root
                        :path @(:path {})
                        :depth depth}))
                  })
                (range agent-count))]

    {
     :type :parallel-colored-exploration
     :agents (count agents)
     :depth depth
     :results (map #((:explore %)) agents)
    }))

;; =============================================================================
;; Section 9: Status and Metadata
;; =============================================================================

(defn colored-sexp-status
  "Return status of colored S-expression system"
  []
  {
   :system "Colored S-Expression Engine"
   :version "1.0.0"
   :features [
     "Self-materializing code execution"
     "Colored terminal visualization"
     "Execution history tracking"
     "Code generation from patterns"
     "Parallel colored exploration"
     "Integration with SICP evaluator"
   ]
   :color-types (count COLOR-TAGS)
   :supports-ansi-colors true
   :status :ready
  })

;; =============================================================================
;; End of sicp/colored-sexp.clj
;; =============================================================================
