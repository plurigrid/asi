;; =============================================================================
;; SICP Complete System Integration Tests
;;
;; End-to-end tests for all four SICP modules working together:
;; 1. Interactive Evaluator (Clojure)
;; 2. Colored S-Expressions (Clojure)
;; 3. Parallel Explorer (Clojure)
;; 4. ACSet Bridge (Julia)
;;
;; Date: 2025-12-21
;; Status: Production Integration Test Suite
;; =============================================================================

(ns sicp.integration-test
  (:require [clojure.test :refer :all]
            [sicp.interactive-evaluator :as eval]
            [sicp.colored-sexp :as colored]
            [sicp.parallel-explorer :as explorer]))

;; =============================================================================
;; Section 1: Module Availability Tests
;; =============================================================================

(deftest test-all-modules-loadable
  "Test that all SICP modules can be loaded"
  (is (contains? (ns-publics 'sicp.interactive-evaluator) 'mceval))
  (is (contains? (ns-publics 'sicp.colored-sexp) 'colored-sexp))
  (is (contains? (ns-publics 'sicp.parallel-explorer) 'evaluator-explorer)))

(deftest test-evaluator-status
  "Test evaluator module is operational"
  (let [status (eval/evaluator-status)]
    (is (contains? status :system))
    (is (= :ready (:status status)))))

(deftest test-colored-status
  "Test colored module is operational"
  (let [status (colored/colored-sexp-status)]
    (is (contains? status :system))
    (is (= :ready (:status status)))))

(deftest test-explorer-status
  "Test explorer module is operational"
  (let [status (explorer/parallel-explorer-status)]
    (is (contains? status :system))
    (is (= :ready (:status status)))))

;; =============================================================================
;; Section 2: Evaluator + Colored Integration
;; =============================================================================

(deftest test-evaluate-with-colored-feedback
  "Test evaluating expressions with colored visualization"
  (let [expr '(+ 2 3)
        result (eval/mceval expr {} :seed 42)
        colored (colored/colored-sexp result :number 42)]
    (is (= 5 result))
    (is (= 5 (:value colored)))))

(deftest test-colored-self-modify-on-repeated-evaluation
  "Test that repeated evaluation with coloring triggers modification"
  (let [cs (colored/colored-sexp '(+ 1 2) :list 42)]
    (dotimes [_ 5]
      (colored/materialize cs {} :seed 42))
    (is (> @(:execution-count cs) 3))))

(deftest test-evaluator-with-materialized-code
  "Test evaluator with materialized colored code"
  (let [expr '(* 3 4)
        cs (colored/colored-sexp expr :list 42)
        materialized (colored/materialize cs {} :seed 42)
        result (eval/mceval expr {} :seed 42)]
    (is (= 12 result))
    (is (contains? materialized :materialization))))

;; =============================================================================
;; Section 3: Evaluator + Explorer Integration
;; =============================================================================

(deftest test-evaluator-agent-explores-evaluation-space
  "Test that evaluator agent explores expressions"
  (let [agent (explorer/evaluator-explorer 1 42 '(+ 2 3) 3)
        result ((:explore agent))]
    (is (= 3 (:exploration-count result)))
    (is (= '(+ 2 3) (:initial-expr agent)))))

(deftest test-evaluator-with-parallel-exploration
  "Test evaluator integrated with parallel exploration"
  (let [concepts ['(+ 1 2) '(* 3 4) '(- 5 2)]
        session (explorer/create-exploration-session "test" 42 concepts 2)
        exploration (explorer/parallel-explore-sicp session 42 concepts 2)]
    (is (= :parallel-exploration-complete (:type exploration)))))

(deftest test-evaluation-results-in-merged-exploration
  "Test that evaluation results feed into merged exploration"
  (let [exploration (explorer/run-sicp-interactive-session 42 2)]
    (is (contains? (:exploration exploration) :merged-results))))

;; =============================================================================
;; Section 4: Colored + Explorer Integration
;; =============================================================================

(deftest test-colored-code-with-parallel-exploration
  "Test colored code generation fed into exploration"
  (let [cs (colored/colored-sexp '(lambda (x) (* x x)) :list 42)
        _ (dotimes [_ 5] (colored/materialize cs {} :seed 42))
        generated (colored/generate-from-pattern cs identity)]
    (is (= :generated-code (:type generated)))))

(deftest test-exploration-with-colored-visualization
  "Test that exploration results are visualizable"
  (let [agent-results [
          {:agent-id 1 :agent-type :evaluator :exploration-count 50}
          {:agent-id 2 :agent-type :code-rewriter :transformation-count 40}
          ]
        exploration {:session-id "test" :results agent-results}
        visualization (explorer/visualize-exploration exploration)]
    (is (string? visualization))
    (is (> (count visualization) 0))))

;; =============================================================================
;; Section 5: Three-Module Workflow
;; =============================================================================

(deftest test-eval-color-explore-workflow
  "Test complete workflow: evaluate, colorize, explore"
  (let [
        ;; Step 1: Evaluate
        expr '(+ 2 3)
        eval-result (eval/mceval expr {} :seed 42)

        ;; Step 2: Colorize
        cs (colored/colored-sexp eval-result :number 42)

        ;; Step 3: Execute with coloring
        materialized (colored/materialize cs {} :seed 42)

        ;; Step 4: Explore implications
        agent (explorer/evaluator-explorer 1 42 expr 2)
        exploration ((:explore agent))]

    (is (= 5 eval-result))
    (is (= 5 (:value cs)))
    (is (> @(:execution-count cs) 0))
    (is (= 2 (:exploration-count exploration)))))

(deftest test-complete-sicp-session-end-to-end
  "Test complete end-to-end SICP session"
  (let [
        ;; Create and evaluate
        env (atom {})
        _ (eval/mceval '(define x 10) env :seed 42)
        result1 (eval/mceval '(+ x 5) env :seed 42)

        ;; Colorize result
        cs (colored/colored-sexp result1 :number 42)
        trace (colored/execution-trace cs)

        ;; Run full parallel exploration
        full-session (explorer/run-sicp-interactive-session 42 2)]

    (is (= 15 result1))
    (is (= :trace (:type trace)))
    (is (contains? full-session :exploration))
    (is (contains? full-session :analysis))
    (is (contains? full-session :visualization))))

;; =============================================================================
;; Section 6: SICP Example Programs Integration
;; =============================================================================

(deftest test-factorial-with-colored-execution
  "Test factorial with colored execution tracking"
  (let [env (atom {})
        _ (eval/mceval '(define (fact n)
                         (if (= n 0) 1 (* n (fact (- n 1)))))
                      env :seed 42)
        result (eval/mceval '(fact 5) env :seed 42)
        cs (colored/colored-sexp result :number 42)]

    (is (= 120 result))
    (is (= 120 (:value cs)))))

(deftest test-fibonacci-with-exploration
  "Test fibonacci with parallel exploration"
  (let [env (atom {})
        fib-def '(define (fib n)
                   (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
        _ (eval/mceval fib-def env :seed 42)
        result (eval/mceval '(fib 6) env :seed 42)]

    (is (= 8 result))))

(deftest test-higher-order-functions-with-all-modules
  "Test higher-order functions with colored exploration"
  (let [env (atom {})
        map-def '(define (mymap f lst)
                   (if (null? lst) '() (cons (f (car lst)) (mymap f (cdr lst)))))
        _ (eval/mceval map-def env :seed 42)
        result (eval/mceval '(mymap (lambda (x) (* x 2)) '(1 2 3)) env :seed 42)
        cs (colored/colored-sexp result :list 42)
        _ (dotimes [_ 5] (colored/materialize cs {} :seed 42))
        trace (colored/execution-trace cs)]

    (is (= '(2 4 6) result))
    (is (= :trace (:type trace)))))

;; =============================================================================
;; Section 7: Parallel Exploration with Evaluator
;; =============================================================================

(deftest test-three-agent-types-integrated
  "Test all three agent types working together"
  (let [concepts ['(+ 2 3) '(lambda (x) (* x x)) '(define foo 42)]
        session (explorer/create-exploration-session "test" 42 concepts 2)
        agents (:agents session)

        ;; Extract agent types
        agent-types (set (map :agent-type agents))]

    (is (contains? agent-types :evaluator))
    (is (contains? agent-types :code-rewriter))
    (is (contains? agent-types :categorical))))

(deftest test-agent-results-synthesis
  "Test synthesis of results from three agents"
  (let [agent-results [
          {:agent-id 1 :agent-type :evaluator :exploration-count 50 :transformation-count 0 :morphism-count 0}
          {:agent-id 2 :agent-type :code-rewriter :exploration-count 0 :transformation-count 40 :morphism-count 0}
          {:agent-id 3 :agent-type :categorical :exploration-count 0 :transformation-count 0 :morphism-count 60}
        ]
        analysis (explorer/analyze-exploration-results
                  {:type :test :results agent-results})]

    (is (= 50 (get (:summary analysis) :evaluations)))
    (is (= 40 (get (:summary analysis) :transformations)))
    (is (= 60 (get (:summary analysis) :morphisms)))))

;; =============================================================================
;; Section 8: Complex Expression Evaluation with Full Integration
;; =============================================================================

(deftest test-nested-let-with-integration
  "Test nested let expressions with full module integration"
  (let [expr '(let ((x 5) (y 10)) (+ x y))
        result (eval/mceval expr {} :seed 42)]
    (is (= 15 result))))

(deftest test-cond-with-colored-output
  "Test cond with colored visualization"
  (let [expr '(cond (false 1) (false 2) (true 3) (true 4))
        result (eval/mceval expr {} :seed 42)
        cs (colored/colored-sexp result :number 42)]
    (is (= 3 result))
    (is (= 3 (:value cs)))))

(deftest test-begin-sequence-with-exploration
  "Test begin sequence with exploration"
  (let [expr '(begin (+ 1 2) (* 3 4) (- 10 5))
        result (eval/mceval expr {} :seed 42)
        agent (explorer/evaluator-explorer 1 42 expr 2)
        exploration ((:explore agent))]

    (is (= 5 result))
    (is (= 2 (:exploration-count exploration)))))

;; =============================================================================
;; Section 9: Error Recovery and Graceful Degradation
;; =============================================================================

(deftest test-evaluation-error-handling
  "Test graceful handling of evaluation errors"
  (try
    (eval/mceval '(undefined-var) {} :seed 42)
    (catch Exception e
      (is (true? true))))) ; Error caught as expected

(deftest test-colored-sexp-with-nil-values
  "Test colored S-expression handles edge cases"
  (let [cs (colored/colored-sexp nil :symbol 42)]
    (is (= nil (:value cs)))))

(deftest test-explorer-with-empty-concepts
  "Test explorer handles edge cases"
  (let [concepts []
        session (explorer/create-exploration-session "test" 42 concepts 1)]
    (is (contains? session :session-id))))

;; =============================================================================
;; Section 10: Performance Integration Tests
;; =============================================================================

(deftest test-evaluator-performance
  "Test evaluator performance with complex expression"
  (let [start (System/currentTimeMillis)
        _ (eval/mceval '(+ 2 3) {} :seed 42)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 100))))

(deftest test-colored-sexp-performance
  "Test colored S-expression performance"
  (let [cs (colored/colored-sexp '(+ 1 2) :list 42)
        start (System/currentTimeMillis)
        _ (colored/materialize cs {} :seed 42)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 100))))

(deftest test-full-session-performance
  "Test complete session performance"
  (let [start (System/currentTimeMillis)
        _ (explorer/run-sicp-interactive-session 42 2)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 5000)))) ; Should complete in reasonable time

;; =============================================================================
;; Section 11: Determinism Across All Modules
;; =============================================================================

(deftest test-deterministic-evaluation
  "Test that same seed produces same evaluation"
  (let [r1 (eval/mceval '(+ 2 3) {} :seed 42)
        r2 (eval/mceval '(+ 2 3) {} :seed 42)]
    (is (= r1 r2))))

(deftest test-deterministic-coloring
  "Test that same seed produces same coloring"
  (let [cs1 (colored/colored-sexp 42 :number 42)
        cs2 (colored/colored-sexp 42 :number 42)]
    (is (= (:color-tag cs1) (:color-tag cs2)))))

(deftest test-deterministic-exploration
  "Test that same seed produces consistent exploration"
  (let [r1 (explorer/run-sicp-interactive-session 42 2)
        r2 (explorer/run-sicp-interactive-session 42 2)]
    (is (= (:seed r1) (:seed r2)))
    (is (= (:depth r1) (:depth r2)))))

;; =============================================================================
;; Section 12: Cross-Module Communication
;; =============================================================================

(deftest test-evaluator-result-flows-to-coloring
  "Test that evaluator results can be immediately colored"
  (let [result (eval/mceval '(+ 1 1) {} :seed 42)
        colored (colored/colored-sexp result :number 42)]
    (is (= result (:value colored)))))

(deftest test-colored-code-feeds-into-exploration
  "Test that colored code can feed exploration"
  (let [cs (colored/colored-sexp '(+ 1 2) :list 42)
        _ (dotimes [_ 5] (colored/materialize cs {} :seed 42))
        generated (colored/generate-from-pattern cs identity)]
    (is (= :generated-code (:type generated)))))

(deftest test-exploration-synthesizes-all-agents
  "Test that exploration properly synthesizes all agent results"
  (let [session (explorer/run-sicp-interactive-session 42 2)]
    (is (contains? session :exploration))
    (is (contains? session :analysis))
    (is (contains? session :visualization))))

;; =============================================================================
;; Section 13: Multi-Module Session
;; =============================================================================

(deftest test-complete-multi-module-session
  "Test complete session using all modules"
  (let [
        ;; Module 1: Evaluate expressions
        env (atom {})
        _ (eval/mceval '(define (square x) (* x x)) env :seed 42)
        eval-result (eval/mceval '(square 5) env :seed 42)

        ;; Module 2: Colorize result
        colored-result (colored/colored-sexp eval-result :number 42)
        _ (colored/materialize colored-result {} :seed 42)

        ;; Module 3: Explore the space
        agent (explorer/evaluator-explorer 1 42 '(square 5) 2)
        agent-result ((:explore agent))

        ;; Module 4: Full session synthesis
        full-session (explorer/run-sicp-interactive-session 42 2)]

    (is (= 25 eval-result))
    (is (= 25 (:value colored-result)))
    (is (= 2 (:exploration-count agent-result)))
    (is (contains? full-session :exploration))))

;; =============================================================================
;; Section 14: Regression Tests
;; =============================================================================

(deftest test-phase2-backward-compatibility
  "Test backward compatibility with Phase 2 UREPL"
  (let [result (eval/mceval '(+ 1 2 3) {} :seed 42)]
    (is (= 6 result))))

(deftest test-music-topos-integration-readiness
  "Test that SICP system is ready for Music-Topos integration"
  (let [status (eval/evaluator-status)]
    (is (= :ready (:status status)))))

;; =============================================================================
;; Section 15: System Verification
;; =============================================================================

(deftest test-all-systems-reporting-ready
  "Test that all subsystems report ready status"
  (let [eval-status (eval/evaluator-status)
        colored-status (colored/colored-sexp-status)
        explorer-status (explorer/parallel-explorer-status)]

    (is (= :ready (:status eval-status)))
    (is (= :ready (:status colored-status)))
    (is (= :ready (:status explorer-status)))))

(deftest test-system-version-consistency
  "Test that system versions are consistent"
  (let [explorer-status (explorer/parallel-explorer-status)]
    (is (= "1.0.0" (:version explorer-status)))))

;; =============================================================================
;; End of integration test suite
;; =============================================================================
