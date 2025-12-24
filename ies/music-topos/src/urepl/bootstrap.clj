(ns urepl.bootstrap
  "UREPL Phase 2: Color-guided bootstrap sequence"
  (:require [clojure.core.async :as async]
            [urepl.repl-connectors :as connectors]
            [urepl.coordinator :as coordinator])
  (:import [java.time Instant]))

;; ============================================================================
;; Color Guidance (SplitMix64)
;; ============================================================================

(defrecord SplitMix64 [^long state])

(defn next-color
  "Generate next color in deterministic golden angle spiral"
  [^SplitMix64 rng]
  (let [state (:state rng)
        ;; SplitMix64 algorithm: next state
        s (bit-xor state 0x9e3779b97f4a7c15)
        t (* (bit-and s 0xbf58476d1ce4e5b9) s)
        z (bit-xor (bit-shift-right t 27) t)

        ;; Convert to hue (0-360 degrees)
        ;; Golden angle: 137.508 degrees
        golden-angle 137.508
        index (mod z 360)
        hue (mod (* index golden-angle) 360.0)

        ;; Generate RGB from hue (simple HSV -> RGB)
        ;; Using 1 for saturation and value
        h (mod (/ hue 60.0) 6.0)
        c 1.0
        x (* c (- 1.0 (Math/abs (- (mod h 2.0) 1.0))))

        [r g b] (cond
                  (<= h 1) [c x 0]
                  (<= h 2) [x c 0]
                  (<= h 3) [0 c x]
                  (<= h 4) [0 x c]
                  (<= h 5) [x 0 c]
                  :else [c 0 x])

        ;; Convert to hex
        hex (format "#%02x%02x%02x"
              (int (* r 255))
              (int (* g 255))
              (int (* b 255)))]

    {:hue hue
     :hex hex
     :rgb [r g b]
     :state (SplitMix64. z)
     :golden-angle golden-angle}))

(defn color-sequence
  "Generate sequence of colors from seed"
  [seed count]
  (let [rng (SplitMix64. seed)]
    (loop [colors [] rng rng n 0]
      (if (< n count)
        (let [color (next-color rng)]
          (recur (conj colors color)
                 (:state color)
                 (inc n)))
        colors))))

;; ============================================================================
;; Bootstrap Steps
;; ============================================================================

(defrecord BootstrapStep
  [name description code dialect color timeout-ms])

(def core-bootstrap-steps
  "Core bootstrap sequence for UREPL Phase 2"
  [
    (BootstrapStep.
      "Initialize Scheme REPL"
      "Start Geiser Scheme REPL and verify connectivity"
      "(display \"UREPL Scheme REPL Ready\\n\")"
      :scheme
      nil
      5000)

    (BootstrapStep.
      "Initialize Clojure REPL"
      "Start nREPL Clojure REPL and verify connectivity"
      "(println \"UREPL Clojure REPL Ready\")"
      :clojure
      nil
      5000)

    (BootstrapStep.
      "Initialize Common Lisp REPL"
      "Start SLIME Common Lisp REPL and verify connectivity"
      "(format t \"UREPL Common Lisp REPL Ready~%\")"
      :lisp
      nil
      5000)

    (BootstrapStep.
      "Set UREPL Version (Scheme)"
      "Define version constant in Scheme"
      "(define *urepl-version* \"0.2.0-alpha\")"
      :scheme
      nil
      5000)

    (BootstrapStep.
      "Set UREPL Version (Clojure)"
      "Define version constant in Clojure"
      "(def *urepl-version* \"0.2.0-alpha\")"
      :clojure
      nil
      5000)

    (BootstrapStep.
      "Set UREPL Version (Common Lisp)"
      "Define version constant in Common Lisp"
      "(defvar *urepl-version* \"0.2.0-alpha\")"
      :lisp
      nil
      5000)

    (BootstrapStep.
      "Load SRFI 2 (List Predicates)"
      "Load standard list predicate functions"
      "(load \"srfi/srfi-2.scm\")"
      :scheme
      nil
      5000)

    (BootstrapStep.
      "Load SRFI 5 (Let Syntax)"
      "Load enhanced let syntax"
      "(load \"srfi/srfi-5.scm\")"
      :scheme
      nil
      5000)

    (BootstrapStep.
      "Load SRFI 26 (Cut/Cute)"
      "Load partial application syntax"
      "(load \"srfi/srfi-26.scm\")"
      :scheme
      nil
      5000)

    (BootstrapStep.
      "Load SRFI 48 (Formatted Output)"
      "Load formatted output functions"
      "(load \"srfi/srfi-48.scm\")"
      :scheme
      nil
      5000)

    (BootstrapStep.
      "Self-Host UREPL Evaluator"
      "Load the UREPL meta-interpreter itself"
      "(load \"src/urepl/evaluator.scm\")"
      :scheme
      nil
      5000)

    (BootstrapStep.
      "Enable Color-Guided Execution"
      "Register color guidance for all future evaluations"
      "(define *urepl-color-guidance* #t)"
      :scheme
      nil
      5000)
  ])

;; ============================================================================
;; Bootstrap Execution
;; ============================================================================

(defn execute-bootstrap-step
  "Execute a single bootstrap step with color guidance"
  [step colors step-index]
  (let [color (nth colors step-index (SplitMix64. 42))
        step-name (:name step)
        code (:code step)
        dialect (:dialect step)

        ;; Execute code based on dialect
        result (try
                 (case dialect
                   :scheme (connectors/eval-scheme-code code)
                   :clojure (connectors/eval-clojure-code code)
                   :lisp (connectors/eval-lisp-code code)
                   {:error "Unknown dialect"})
                 (catch Exception e
                   {:error (.getMessage e)}))]

    {:step-index step-index
     :name step-name
     :dialect dialect
     :color (if (map? color) color {:hex "#000000"})
     :code code
     :result result
     :success (not (:error result))
     :timestamp (Instant/now)}))

(defn run-bootstrap-sequence
  "Run complete bootstrap sequence with color guidance"
  [& {:keys [seed steps] :or {seed 42 steps core-bootstrap-steps}}]
  (let [color-seq (color-sequence seed (count steps))
        start-time (Instant/now)]

    (println "")
    (println "🎨 UREPL Phase 2 Bootstrap Sequence")
    (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    (println (format "Seed: %d | Color Spiral: Golden Angle (137.508°)" seed))
    (println "")

    ;; Execute all steps in parallel
    (let [results (mapv (fn [idx step]
                         (println (format "  [%d] %s" (inc idx) (:name step)))
                         (execute-bootstrap-step step color-seq idx))
                       (range (count steps))
                       steps)

          successful (count (filter :success results))
          total (count results)
          elapsed-ms (- (.toEpochMilli (Instant/now))
                        (.toEpochMilli start-time))]

      (println "")
      (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
      (println (format "✓ Bootstrap Complete: %d/%d steps successful" successful total))
      (println (format "  Duration: %d ms" elapsed-ms))
      (println "")

      ;; Return detailed results
      {:success (= successful total)
       :steps-completed successful
       :steps-total total
       :duration-ms elapsed-ms
       :seed seed
       :color-sequence color-seq
       :results results
       :timestamp (Instant/now)})))

;; ============================================================================
;; Advanced Bootstrap Configurations
;; ============================================================================

(defn bootstrap-scheme-only
  "Bootstrap only Scheme REPL"
  []
  (let [scheme-steps (filter #(= :scheme (:dialect %)) core-bootstrap-steps)]
    (run-bootstrap-sequence :steps scheme-steps)))

(defn bootstrap-clojure-only
  "Bootstrap only Clojure REPL"
  []
  (let [clojure-steps (filter #(= :clojure (:dialect %)) core-bootstrap-steps)]
    (run-bootstrap-sequence :steps clojure-steps)))

(defn bootstrap-lisp-only
  "Bootstrap only Common Lisp REPL"
  []
  (let [lisp-steps (filter #(= :lisp (:dialect %)) core-bootstrap-steps)]
    (run-bootstrap-sequence :steps lisp-steps)))

(defn bootstrap-minimal
  "Minimal bootstrap: just REPL initialization"
  []
  (let [minimal-steps (take 3 core-bootstrap-steps)]
    (run-bootstrap-sequence :steps minimal-steps)))

(defn bootstrap-srfis-only
  "Bootstrap only SRFI loading"
  []
  (let [srfi-steps (filter #(str/includes? (:name %) "SRFI") core-bootstrap-steps)]
    (run-bootstrap-sequence :steps srfi-steps)))

;; ============================================================================
;; Bootstrap Validation
;; ============================================================================

(defn validate-bootstrap
  "Validate that bootstrap was successful"
  [bootstrap-result]
  (and
    (:success bootstrap-result)
    (= (:steps-completed bootstrap-result) (:steps-total bootstrap-result))
    (every? :success (:results bootstrap-result))))

(defn bootstrap-summary
  "Print human-readable bootstrap summary"
  [bootstrap-result]
  (let [{:keys [success steps-completed steps-total duration-ms]} bootstrap-result]
    (println "")
    (println "UREPL Phase 2 Bootstrap Summary")
    (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    (println (format "  Status: %s" (if success "✓ SUCCESS" "✗ FAILED")))
    (println (format "  Steps: %d/%d completed" steps-completed steps-total))
    (println (format "  Time: %d ms" duration-ms))

    (when-let [results (:results bootstrap-result)]
      (println "")
      (println "  Step Details:")
      (doseq [{:keys [name dialect color success]} results]
        (let [status (if success "✓" "✗")]
          (println (format "    %s [%-7s] %s %s"
                           status
                           (name dialect)
                           name
                           (if (:hex color) (format "(%s)" (:hex color)) ""))))))

    (println "")
    bootstrap-result))

;; ============================================================================
;; Development and Testing
;; ============================================================================

(comment
  ;; Generate color sequence
  (def colors (color-sequence 42 12))
  (doseq [c colors] (println c))

  ;; Run full bootstrap
  (def result (run-bootstrap-sequence))
  (bootstrap-summary result)

  ;; Run scheme-only bootstrap
  (def result (bootstrap-scheme-only))

  ;; Validate bootstrap
  (validate-bootstrap result)

  ;; Run minimal bootstrap
  (bootstrap-minimal)
)
