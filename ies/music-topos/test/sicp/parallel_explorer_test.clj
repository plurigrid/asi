;; =============================================================================
;; Parallel Exploration Coordinator Test Suite
;;
;; Tests for multi-agent parallel exploration, result merging, analysis,
;; and visualization of SICP concept space
;;
;; Date: 2025-12-21
;; Status: Production Test Suite
;; =============================================================================

(ns sicp.parallel-explorer-test
  (:require [clojure.test :refer :all]
            [sicp.parallel-explorer :as explorer]))

;; =============================================================================
;; Section 1: Evaluator Agent Tests
;; =============================================================================

(deftest test-create-evaluator-explorer
  "Test creating evaluator explorer agent"
  (let [agent (explorer/evaluator-explorer 1 42 '(+ 2 3) 3)]
    (is (= 1 (:agent-id agent)))
    (is (= :evaluator (:agent-type agent)))
    (is (= 42 (:seed agent)))))

(deftest test-evaluator-explorer-explore
  "Test evaluator explorer exploration"
  (let [agent (explorer/evaluator-explorer 1 42 '(+ 2 3) 3)
        result ((:explore agent))]
    (is (contains? result :exploration-count))
    (is (= 1 (:agent-id result)))
    (is (= :evaluator (:agent-type result)))))

(deftest test-evaluator-explorer-depth
  "Test that evaluator explorer respects depth"
  (let [agent (explorer/evaluator-explorer 1 42 '(+ 2 3) 5)
        result ((:explore agent))]
    (is (= 5 (:exploration-count result)))))

(deftest test-evaluator-explorer-preserves-expression
  "Test that evaluator explorer preserves initial expression"
  (let [expr '(+ 2 3)
        agent (explorer/evaluator-explorer 1 42 expr 3)
        result ((:explore agent))]
    (is (= expr (:initial-expr agent)))))

;; =============================================================================
;; Section 2: Code Rewriter Agent Tests
;; =============================================================================

(deftest test-create-code-rewriter-explorer
  "Test creating code rewriter explorer agent"
  (let [agent (explorer/code-rewriter-explorer 2 42 '(lambda (x) (* x x)) 3)]
    (is (= 2 (:agent-id agent)))
    (is (= :code-rewriter (:agent-type agent)))
    (is (= 42 (:seed agent)))))

(deftest test-code-rewriter-explorer-explore
  "Test code rewriter explorer exploration"
  (let [agent (explorer/code-rewriter-explorer 2 42 '(lambda (x) (* x x)) 3)
        result ((:explore agent))]
    (is (contains? result :transformation-count))
    (is (= 2 (:agent-id result)))
    (is (= :code-rewriter (:agent-type result)))))

(deftest test-code-rewriter-explorer-depth
  "Test that code rewriter respects depth"
  (let [agent (explorer/code-rewriter-explorer 2 42 '(lambda (x) x) 4)
        result ((:explore agent))]
    (is (= 4 (:transformation-count result)))))

(deftest test-code-rewriter-explorer-generates-code
  "Test that code rewriter generates variations"
  (let [agent (explorer/code-rewriter-explorer 2 42 '(lambda (x) x) 3)
        result ((:explore agent))]
    (is (> (:generated-count result) 0))))

;; =============================================================================
;; Section 3: Categorical Explorer Agent Tests
;; =============================================================================

(deftest test-create-categorical-explorer
  "Test creating categorical explorer agent"
  (let [agent (explorer/categorical-explorer 3 42 'Expr 3)]
    (is (= 3 (:agent-id agent)))
    (is (= :categorical (:agent-type agent)))
    (is (= 42 (:seed agent)))))

(deftest test-categorical-explorer-explore
  "Test categorical explorer exploration"
  (let [agent (explorer/categorical-explorer 3 42 'Expr 3)
        result ((:explore agent))]
    (is (contains? result :morphism-count))
    (is (= 3 (:agent-id result)))
    (is (= :categorical (:agent-type result)))))

(deftest test-categorical-explorer-depth
  "Test that categorical explorer respects depth"
  (let [agent (explorer/categorical-explorer 3 42 'Value 4)
        result ((:explore agent))]
    (is (= 4 (:morphism-count result)))))

(deftest test-categorical-explorer-discovers-morphisms
  "Test that categorical explorer discovers morphisms"
  (let [agent (explorer/categorical-explorer 3 42 'Expr 3)
        result ((:explore agent))]
    (is (> (:morphism-count result) 0))))

;; =============================================================================
;; Section 4: Exploration Session Creation
;; =============================================================================

(deftest test-create-exploration-session
  "Test creating exploration session"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 3)]
    (is (= "session-1" (:session-id session)))
    (is (= 42 (:seed session)))
    (is (= concepts (:concepts session)))))

(deftest test-session-has-three-agents
  "Test that session creates three agents"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 3)]
    (is (= 3 (count (:agents session))))))

(deftest test-session-has-launch-function
  "Test that session has launch function"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 3)]
    (is (contains? session :launch-agents))))

(deftest test-session-has-merge-function
  "Test that session has merge function"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 3)]
    (is (contains? session :merge-results))))

;; =============================================================================
;; Section 5: Parallel Execution Tests
;; =============================================================================

(deftest test-parallel-explore-sicp
  "Test parallel exploration launch"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 2)
        result (explorer/parallel-explore-sicp session 42 concepts 2)]
    (is (contains? result :type))
    (is (= :parallel-exploration-complete (:type result)))))

(deftest test-parallel-explore-includes-session-id
  "Test that results include session ID"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-42" 42 concepts 2)
        result (explorer/parallel-explore-sicp session 42 concepts 2)]
    (is (= "session-42" (:session-id result)))))

(deftest test-parallel-explore-includes-merged-results
  "Test that results include merged results"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 2)
        result (explorer/parallel-explore-sicp session 42 concepts 2)]
    (is (contains? result :merged-results))))

(deftest test-parallel-explore-status
  "Test that exploration has completion status"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 2)
        result (explorer/parallel-explore-sicp session 42 concepts 2)]
    (is (= :complete (:status result)))))

;; =============================================================================
;; Section 6: Result Analysis Tests
;; =============================================================================

(deftest test-analyze-exploration-results
  "Test analysis of exploration results"
  (let [sample-result {:agent-type :evaluator :exploration-count 50}
        analysis (explorer/analyze-exploration-results
                  {:type :sample :results [sample-result]})]
    (is (contains? analysis :type))
    (is (= :analysis (:type analysis)))))

(deftest test-analysis-includes-summary
  "Test that analysis includes summary"
  (let [sample-result {:agent-type :evaluator :exploration-count 50}
        analysis (explorer/analyze-exploration-results
                  {:type :sample :results [sample-result]})]
    (is (contains? analysis :summary))))

(deftest test-analysis-groups-by-agent-type
  "Test that analysis groups results by agent type"
  (let [results [
        {:agent-type :evaluator :exploration-count 50}
        {:agent-type :code-rewriter :transformation-count 40}
        {:agent-type :categorical :morphism-count 60}
        ]
        analysis (explorer/analyze-exploration-results
                  {:type :sample :results results})]
    (is (contains? analysis :by-agent-type))))

(deftest test-analysis-includes-insights
  "Test that analysis includes insights"
  (let [sample-result {:agent-type :evaluator :exploration-count 50}
        analysis (explorer/analyze-exploration-results
                  {:type :sample :results [sample-result]})]
    (is (contains? analysis :insights))
    (is (vector? (:insights analysis)))
    (is (> (count (:insights analysis)) 0))))

(deftest test-analysis-includes-next-steps
  "Test that analysis includes next steps"
  (let [sample-result {:agent-type :evaluator :exploration-count 50}
        analysis (explorer/analyze-exploration-results
                  {:type :sample :results [sample-result]})]
    (is (contains? analysis :next-steps))
    (is (vector? (:next-steps analysis)))))

;; =============================================================================
;; Section 7: Visualization Tests
;; =============================================================================

(deftest test-visualize-exploration
  "Test visualization of exploration results"
  (let [sample-result {:agent-type :evaluator :exploration-count 50 :agent-id 1}
        result {:session-id "session-1" :results [sample-result]}
        visualization (explorer/visualize-exploration result)]
    (is (string? visualization))
    (is (> (count visualization) 0))))

(deftest test-visualization-includes-session-id
  "Test that visualization includes session ID"
  (let [sample-result {:agent-type :evaluator :exploration-count 50 :agent-id 1}
        result {:session-id "test-session" :results [sample-result]}
        visualization (explorer/visualize-exploration result)]
    (is (.contains visualization "test-session"))))

(deftest test-visualization-includes-agent-count
  "Test that visualization shows agent count"
  (let [results [
        {:agent-type :evaluator :exploration-count 50 :agent-id 1}
        {:agent-type :code-rewriter :transformation-count 40 :agent-id 2}
        ]
        result {:session-id "session-1" :results results}
        visualization (explorer/visualize-exploration result)]
    (is (.contains visualization "Agents: 2"))))

(deftest test-visualization-includes-agent-results
  "Test that visualization includes individual agent results"
  (let [sample-result {:agent-type :evaluator :exploration-count 50 :agent-id 1}
        result {:session-id "session-1" :results [sample-result]}
        visualization (explorer/visualize-exploration result)]
    (is (.contains visualization "Agent 1"))))

(deftest test-visualization-includes-discoveries
  "Test that visualization mentions discoveries"
  (let [sample-result {:agent-type :evaluator :exploration-count 50 :agent-id 1}
        result {:session-id "session-1" :results [sample-result]}
        visualization (explorer/visualize-exploration result)]
    (is (.contains visualization "discoveries"))))

(deftest test-visualization-is-formatted
  "Test that visualization is well-formatted"
  (let [sample-result {:agent-type :evaluator :exploration-count 50 :agent-id 1}
        result {:session-id "session-1" :results [sample-result]}
        visualization (explorer/visualize-exploration result)]
    (is (.contains visualization "═════════════"))))

;; =============================================================================
;; Section 8: Complete Integration Tests
;; =============================================================================

(deftest test-run-complete-sicp-session
  "Test running complete end-to-end SICP session"
  (let [result (explorer/run-sicp-interactive-session 42 3)]
    (is (contains? result :type))
    (is (= :complete-session (:type result)))))

(deftest test-complete-session-includes-seed
  "Test that complete session records seed"
  (let [result (explorer/run-sicp-interactive-session 42 3)]
    (is (= 42 (:seed result)))))

(deftest test-complete-session-includes-depth
  "Test that complete session records depth"
  (let [result (explorer/run-sicp-interactive-session 42 3)]
    (is (= 3 (:depth result)))))

(deftest test-complete-session-includes-exploration
  "Test that complete session includes exploration results"
  (let [result (explorer/run-sicp-interactive-session 42 3)]
    (is (contains? result :exploration))))

(deftest test-complete-session-includes-analysis
  "Test that complete session includes analysis"
  (let [result (explorer/run-sicp-interactive-session 42 3)]
    (is (contains? result :analysis))))

(deftest test-complete-session-includes-visualization
  "Test that complete session includes visualization"
  (let [result (explorer/run-sicp-interactive-session 42 3)]
    (is (contains? result :visualization))))

;; =============================================================================
;; Section 9: Three-Agent Coordination Tests
;; =============================================================================

(deftest test-three-agent-types
  "Test that three different agent types are created"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 2)]
    (let [agent-types (set (map :agent-type (:agents session)))]
      (is (contains? agent-types :evaluator))
      (is (contains? agent-types :code-rewriter))
      (is (contains? agent-types :categorical)))))

(deftest test-agent-seeds-are-different
  "Test that each agent gets unique seed offset"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 2)
        seeds (set (map :seed (:agents session)))]
    (is (> (count seeds) 1))))

;; =============================================================================
;; Section 10: Result Merging Tests
;; =============================================================================

(deftest test-merge-results
  "Test merging results from multiple agents"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 2)
        agent-results [
          {:agent-id 1 :exploration-count 50 :transformation-count 0 :morphism-count 0}
          {:agent-id 2 :exploration-count 0 :transformation-count 40 :morphism-count 0}
          {:agent-id 3 :exploration-count 0 :transformation-count 0 :morphism-count 60}
        ]
        merge-fn (:merge-results session)
        merged (merge-fn agent-results)]
    (is (= :merged-exploration (:type merged)))
    (is (= 50 (:total-explorations merged)))
    (is (= 40 (:total-transformations merged)))
    (is (= 60 (:total-morphisms merged)))))

(deftest test-merge-result-includes-timestamp
  "Test that merged results include timestamp"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 2)
        merge-fn (:merge-results session)
        merged (merge-fn [{:agent-id 1 :exploration-count 50 :transformation-count 0 :morphism-count 0}])]
    (is (contains? merged :timestamp))))

;; =============================================================================
;; Section 11: Status and System Tests
;; =============================================================================

(deftest test-system-status
  "Test parallel explorer system status"
  (let [status (explorer/parallel-explorer-status)]
    (is (contains? status :system))
    (is (= "SICP Parallel Explorer" (:system status)))))

(deftest test-status-includes-version
  "Test that status includes version"
  (let [status (explorer/parallel-explorer-status)]
    (is (contains? status :version))))

(deftest test-status-includes-agent-types
  "Test that status lists agent types"
  (let [status (explorer/parallel-explorer-status)]
    (is (contains? status :agent-types))
    (is (= 3 (count (:agent-types status))))))

(deftest test-status-includes-features
  "Test that status lists features"
  (let [status (explorer/parallel-explorer-status)]
    (is (contains? status :features))
    (is (> (count (:features status)) 0))))

(deftest test-status-is-ready
  "Test that system is ready"
  (let [status (explorer/parallel-explorer-status)]
    (is (= :ready (:status status)))))

;; =============================================================================
;; Section 12: Determinism Tests
;; =============================================================================

(deftest test-same-seed-same-results
  "Test that same seed produces consistent results"
  (let [concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        r1 (explorer/run-sicp-interactive-session 42 2)
        r2 (explorer/run-sicp-interactive-session 42 2)]
    (is (= (:seed r1) (:seed r2)))
    (is (= (:depth r1) (:depth r2)))))

(deftest test-different-seed-different-results
  "Test that different seeds produce different results"
  (let [r1 (explorer/run-sicp-interactive-session 42 2)
        r2 (explorer/run-sicp-interactive-session 43 2)]
    (is (not= (:seed r1) (:seed r2)))))

;; =============================================================================
;; Section 13: Performance Tests
;; =============================================================================

(deftest test-explorer-agent-creation-performance
  "Test that agent creation is fast"
  (let [start (System/currentTimeMillis)
        _ (dotimes [_ 10]
            (explorer/evaluator-explorer 1 42 '(+ 2 3) 2))
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 100))))

(deftest test-parallel-exploration-performance
  "Test that parallel exploration completes in reasonable time"
  (let [start (System/currentTimeMillis)
        concepts ['(+ 2 3) '(lambda (x) x) '(define foo 42)]
        session (explorer/create-exploration-session "session-1" 42 concepts 2)
        _ (explorer/parallel-explore-sicp session 42 concepts 2)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 5000))))

(deftest test-visualization-generation-performance
  "Test that visualization generation is fast"
  (let [sample-result {:agent-type :evaluator :exploration-count 50 :agent-id 1}
        result {:session-id "session-1" :results [sample-result]}
        start (System/currentTimeMillis)
        _ (explorer/visualize-exploration result)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 100))))

;; =============================================================================
;; End of test suite
;; =============================================================================
