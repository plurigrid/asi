;; =============================================================================
;; Parallelism Measurement Test Suite
;;
;; Tests for measuring and benchmarking parallel execution
;;
;; Date: 2025-12-21
;; Status: Production Test Suite
;; =============================================================================

(ns parallel.parallelism-measurement-test
  (:require [clojure.test :refer :all]
            [parallel.parallelism-measurement :as pm]))

;; =============================================================================
;; Section 1: Basic Timing and Measurement Tests
;; =============================================================================

(deftest test-measure-time-returns-result
  "Test that measure-time captures result"
  (let [measurement (pm/measure-time #(+ 1 2))]
    (is (contains? measurement :result))
    (is (= 3 (:result measurement)))))

(deftest test-measure-time-captures-elapsed
  "Test that measure-time captures elapsed time"
  (let [measurement (pm/measure-time #(Thread/sleep 10))]
    (is (contains? measurement :elapsed-ms))
    (is (>= (:elapsed-ms measurement) 9))))

(deftest test-measure-time-verbose-structure
  "Test verbose measurement structure"
  (let [measurement (pm/measure-time-verbose "test" #(+ 1 1))]
    (is (contains? measurement :label))
    (is (contains? measurement :result))
    (is (contains? measurement :elapsed-ms))
    (is (contains? measurement :elapsed-us))
    (is (contains? measurement :elapsed-ns))))

(deftest test-measure-time-accuracy
  "Test measurement accuracy within reasonable bounds"
  (let [measurement (pm/measure-time #(Thread/sleep 20))]
    (is (> (:elapsed-ms measurement) 15))
    (is (< (:elapsed-ms measurement) 100))))

;; =============================================================================
;; Section 2: Sequential vs Parallel Tests
;; =============================================================================

(deftest test-sequential-execution
  "Test sequential execution measurement"
  (let [result (pm/measure-sequential
                #(do (Thread/sleep 5) "op1")
                #(do (Thread/sleep 5) "op2")
                #(do (Thread/sleep 5) "op3"))]
    (is (contains? result :elapsed-ms))
    (is (>= (:elapsed-ms result) 14))))

(deftest test-parallel-async-execution
  "Test parallel async execution"
  (let [result (pm/measure-parallel-async
                #(do (Thread/sleep 5) "op1")
                #(do (Thread/sleep 5) "op2")
                #(do (Thread/sleep 5) "op3"))]
    (is (contains? result :elapsed-ms))
    (is (< (:elapsed-ms result) 15))))

(deftest test-parallel-async-faster-than-sequential
  "Test that parallel is faster than sequential"
  (let [seq-result (pm/measure-sequential
                    #(do (Thread/sleep 10) 1)
                    #(do (Thread/sleep 10) 2)
                    #(do (Thread/sleep 10) 3))
        par-result (pm/measure-parallel-async
                    #(do (Thread/sleep 10) 1)
                    #(do (Thread/sleep 10) 2)
                    #(do (Thread/sleep 10) 3))]
    (is (< (:elapsed-ms par-result) (:elapsed-ms seq-result)))))

;; =============================================================================
;; Section 3: Speedup Calculation Tests
;; =============================================================================

(deftest test-calculate-speedup
  "Test speedup calculation"
  (let [speedup (pm/calculate-speedup 30.0 10.0)]
    (is (= 300.0 speedup))))

(deftest test-calculate-speedup-less-than-one
  "Test speedup when parallel slower than sequential"
  (let [speedup (pm/calculate-speedup 20.0 30.0)]
    (is (< speedup 100.0))))

(deftest test-calculate-efficiency
  "Test efficiency calculation"
  (let [efficiency (pm/calculate-efficiency 300.0 3)]
    (is (= 100.0 efficiency))))

(deftest test-calculate-efficiency-less-than-optimal
  "Test efficiency less than 100%"
  (let [efficiency (pm/calculate-efficiency 250.0 3)]
    (is (< efficiency 100.0))))

;; =============================================================================
;; Section 4: Parallelism Analysis Tests
;; =============================================================================

(deftest test-analyze-parallelism-structure
  "Test parallelism analysis structure"
  (let [seq-result (pm/measure-sequential #(Thread/sleep 5) #(Thread/sleep 5) #(Thread/sleep 5))
        par-result (pm/measure-parallel-async #(Thread/sleep 5) #(Thread/sleep 5) #(Thread/sleep 5))
        analysis (pm/analyze-parallelism seq-result par-result :num-processors 3)]
    (is (contains? analysis :sequential-time-ms))
    (is (contains? analysis :parallel-time-ms))
    (is (contains? analysis :speedup))
    (is (contains? analysis :efficiency))
    (is (contains? analysis :num-processors))))

(deftest test-analyze-parallelism-values
  "Test that analysis produces reasonable values"
  (let [seq-result (pm/measure-sequential #(Thread/sleep 5) #(Thread/sleep 5) #(Thread/sleep 5))
        par-result (pm/measure-parallel-async #(Thread/sleep 5) #(Thread/sleep 5) #(Thread/sleep 5))
        analysis (pm/analyze-parallelism seq-result par-result :num-processors 3)]
    (is (> (:speedup analysis) 0))
    (is (> (:efficiency analysis) 0))
    (is (= 3 (:num-processors analysis)))))

;; =============================================================================
;; Section 5: Agent Benchmark Tests
;; =============================================================================

(deftest test-sicp-benchmark-structure
  "Test SICP agent benchmark structure"
  (let [result (pm/benchmark-sicp-agents 42 2 :iterations 2)]
    (is (= :sicp-agents (:benchmark result)))
    (is (= 42 (:seed result)))
    (is (= 2 (:depth result)))
    (is (= 2 (:iterations result)))
    (is (contains? result :results))
    (is (contains? result :average-speedup))
    (is (contains? result :average-efficiency))))

(deftest test-discopy-benchmark-structure
  "Test Discopy agent benchmark structure"
  (let [result (pm/benchmark-discopy-agents 42 2 :iterations 2)]
    (is (= :discopy-agents (:benchmark result)))
    (is (seq (:results result)))))

(deftest test-github-benchmark-structure
  "Test GitHub agent benchmark structure"
  (let [result (pm/benchmark-github-agents 42 2 :iterations 2)]
    (is (= :github-agents (:benchmark result)))
    (is (seq (:results result)))))

(deftest test-benchmark-speedup-is-positive
  "Test that benchmark speedup is positive"
  (let [result (pm/benchmark-sicp-agents 42 2 :iterations 1)]
    (is (> (:average-speedup result) 0))))

;; =============================================================================
;; Section 6: Cross-System Analysis Tests
;; =============================================================================

(deftest test-run-all-benchmarks-structure
  "Test all benchmarks structure"
  (let [result (pm/run-all-benchmarks :seed 42 :depth 2 :iterations 1)]
    (is (contains? result :timestamp))
    (is (contains? result :seed))
    (is (contains? result :depth))
    (is (contains? result :iterations))
    (is (contains? result :sicp))
    (is (contains? result :discopy))
    (is (contains? result :github))))

(deftest test-compare-system-parallelism-structure
  "Test system comparison structure"
  (let [benchmarks (pm/run-all-benchmarks :iterations 1)
        comparison (pm/compare-system-parallelism benchmarks)]
    (is (= :cross-system-parallelism-analysis (:type comparison)))
    (is (contains? comparison :systems))
    (is (contains? comparison :best-speedup))
    (is (contains? comparison :best-system))))

(deftest test-comparison-identifies-best-system
  "Test that comparison identifies best system"
  (let [benchmarks (pm/run-all-benchmarks :iterations 1)
        comparison (pm/compare-system-parallelism benchmarks)]
    (is (keyword? (:best-system comparison)))
    (is (or (= :sicp (:best-system comparison))
            (= :discopy (:best-system comparison))
            (= :github (:best-system comparison))))))

;; =============================================================================
;; Section 7: Scaling Analysis Tests
;; =============================================================================

(deftest test-benchmark-scaling-structure
  "Test scaling benchmark structure"
  (let [result (pm/benchmark-scaling [1 2 3])]
    (is (= :scaling-analysis (:type result)))
    (is (contains? result :results))
    (is (contains? result :speedup-trend))
    (is (contains? result :efficiency-trend))))

(deftest test-benchmark-scaling-results
  "Test scaling benchmark has results"
  (let [result (pm/benchmark-scaling [1 2 3])]
    (is (= 3 (count (:results result))))))

(deftest test-scaling-speedup-trend
  "Test scaling speedup trend captured"
  (let [result (pm/benchmark-scaling [1 2 3])]
    (is (= 3 (count (:speedup-trend result))))
    (is (every? number? (:speedup-trend result)))))

;; =============================================================================
;; Section 8: Coordination Overhead Tests
;; =============================================================================

(deftest test-measure-coordination-overhead-structure
  "Test coordination overhead measurement structure"
  (let [result (pm/measure-coordination-overhead 3)]
    (is (= :coordination-overhead (:type result)))
    (is (contains? result :measurements))
    (is (contains? result :average-overhead))
    (is (contains? result :max-overhead))
    (is (contains? result :min-overhead))))

(deftest test-coordination-overhead-measurements
  "Test coordination overhead has measurements"
  (let [result (pm/measure-coordination-overhead 5)]
    (is (= 5 (count (:measurements result))))))

(deftest test-coordination-overhead-values
  "Test coordination overhead values are positive"
  (let [result (pm/measure-coordination-overhead 3)]
    (is (>= (:average-overhead result) 0))
    (is (>= (:max-overhead result) (:min-overhead result))))

;; =============================================================================
;; Section 9: Reporting Tests
;; =============================================================================

(deftest test-format-speedup-table-is-string
  "Test speedup table formatting"
  (let [benchmarks (pm/run-all-benchmarks :iterations 1)
        comparison (pm/compare-system-parallelism benchmarks)
        formatted (pm/format-speedup-table comparison)]
    (is (string? formatted))
    (is (.contains formatted "SICP"))
    (is (.contains formatted "Discopy"))
    (is (.contains formatted "GitHub"))))

(deftest test-format-scaling-table-is-string
  "Test scaling table formatting"
  (let [scaling (pm/benchmark-scaling [1 2 3])
        formatted (pm/format-scaling-table scaling)]
    (is (string? formatted))
    (is (.contains formatted "Agents"))))

(deftest test-format-overhead-report-is-string
  "Test overhead report formatting"
  (let [overhead (pm/measure-coordination-overhead 3)
        formatted (pm/format-overhead-report overhead)]
    (is (string? formatted))
    (is (.contains formatted "Overhead"))))

(deftest test-generate-comprehensive-report-structure
  "Test comprehensive report structure"
  (let [benchmarks (pm/run-all-benchmarks :iterations 1)
        report (pm/generate-parallelism-report benchmarks)]
    (is (= :comprehensive-parallelism-report (:type report)))
    (is (contains? report :benchmark-results))
    (is (contains? report :comparison))
    (is (contains? report :scaling))
    (is (contains? report :coordination-overhead))
    (is (contains? report :summary))))

;; =============================================================================
;; Section 10: Realistic Workload Tests
;; =============================================================================

(deftest test-simulate-agent-workload-structure
  "Test agent workload simulation structure"
  (let [workload (pm/simulate-agent-workload 1 10 :iterations 2)]
    (is (contains? workload :agent-id))
    (is (contains? workload :total-work-ms))
    (is (contains? workload :measurements))
    (is (contains? workload :average-ms))))

(deftest test-benchmark-realistic-workload-structure
  "Test realistic workload benchmark"
  (let [result (pm/benchmark-realistic-parallel-workload :iterations 2)]
    (is (= :realistic-workload (:benchmark result)))
    (is (contains? result :results))
    (is (contains? result :average-speedup))
    (is (contains? result :average-efficiency))))

;; =============================================================================
;; Section 11: Statistical Analysis Tests
;; =============================================================================

(deftest test-calculate-statistics-structure
  "Test statistics calculation structure"
  (let [stats (pm/calculate-statistics [100.0 100.0 100.0 100.0 100.0])]
    (is (contains? stats :count))
    (is (contains? stats :mean))
    (is (contains? stats :median))
    (is (contains? stats :min))
    (is (contains? stats :max))
    (is (contains? stats :stddev))))

(deftest test-calculate-statistics-values
  "Test statistics calculation values"
  (let [stats (pm/calculate-statistics [100.0 100.0 100.0])]
    (is (= 3 (:count stats)))
    (is (= 100.0 (:mean stats)))
    (is (= 100.0 (:median stats)))))

(deftest test-analyze-speedup-distribution-structure
  "Test speedup distribution analysis"
  (let [benchmarks (pm/run-all-benchmarks :iterations 2)
        analysis (pm/analyze-speedup-distribution benchmarks :sicp)]
    (is (contains? analysis :system))
    (is (contains? analysis :speedups))
    (is (contains? analysis :statistics))))

;; =============================================================================
;; Section 12: Performance and Bounds Tests
;; =============================================================================

(deftest test-measurements-complete-in-reasonable-time
  "Test that all measurements complete quickly"
  (let [start (System/currentTimeMillis)
        _ (pm/run-all-benchmarks :iterations 1)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 5000))))

(deftest test-speedup-values-are-reasonable
  "Test that speedup values are in expected range"
  (let [benchmarks (pm/run-all-benchmarks :iterations 1)
        sicp-speedup (get-in benchmarks [:sicp :average-speedup])]
    (is (>= sicp-speedup 0))
    (is (<= sicp-speedup 500))))

(deftest test-efficiency-values-are-reasonable
  "Test that efficiency values are bounded"
  (let [benchmarks (pm/run-all-benchmarks :iterations 1)
        sicp-eff (get-in benchmarks [:sicp :average-efficiency])]
    (is (>= sicp-eff 0))
    (is (<= sicp-eff 200))))

;; =============================================================================
;; Section 13: Edge Cases
;; =============================================================================

(deftest test-parallel-with-zero-work
  "Test parallel execution with minimal work"
  (let [result (pm/measure-parallel-async #(do 1) #(do 2) #(do 3))]
    (is (contains? result :elapsed-ms))))

(deftest test-sequential-with-uneven-work
  "Test sequential with different workload times"
  (let [result (pm/measure-sequential
                #(Thread/sleep 5)
                #(Thread/sleep 10)
                #(Thread/sleep 15))]
    (is (>= (:elapsed-ms result) 29))))

(deftest test-scaling-single-agent
  "Test scaling with single agent"
  (let [result (pm/benchmark-scaling [1])]
    (is (= 1 (count (:results result))))))

;; =============================================================================
;; End of test suite
;; =============================================================================
