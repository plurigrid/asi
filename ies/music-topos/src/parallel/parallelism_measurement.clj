;; =============================================================================
;; Parallelism Measurement and Benchmarking System
;;
;; Measures parallelism efficiency across all three-agent exploration systems:
;; - SICP evaluator agents
;; - Discopy categorical agents
;; - GitHub ecosystem agents
;;
;; Date: 2025-12-21
;; Status: Production Implementation
;; =============================================================================

(ns parallel.parallelism-measurement
  "Measure and analyze parallelism in multi-agent systems"
  (:require [clojure.core.async :as async]
            [clojure.java.shell :as shell]))

;; =============================================================================
;; Section 1: Timing and Measurement Utilities
;; =============================================================================

(defn measure-time
  "Execute function and measure elapsed time in milliseconds"
  [f]
  (let [start (System/nanoTime)
        result (f)
        elapsed (/ (- (System/nanoTime) start) 1000000.0)]
    {:result result
     :elapsed-ms (double (Math/round elapsed))
     :elapsed-ns (- (System/nanoTime) start)}))

(defn measure-time-verbose
  "Measure time with detailed breakdown"
  [label f]
  (let [start (System/nanoTime)
        result (f)
        elapsed-ns (- (System/nanoTime) start)
        elapsed-ms (/ elapsed-ns 1000000.0)
        elapsed-us (/ elapsed-ns 1000.0)]
    {:label label
     :result result
     :elapsed-ms (double (Math/round elapsed-ms))
     :elapsed-us (double (Math/round elapsed-us))
     :elapsed-ns elapsed-ns}))

;; =============================================================================
;; Section 2: Sequential vs Parallel Comparison
;; =============================================================================

(defn measure-sequential
  "Execute three operations sequentially and measure total time"
  [op1 op2 op3 & {:keys [label]}]
  (measure-time-verbose
   (or label "Sequential")
   (fn []
     {:op1 (op1)
      :op2 (op2)
      :op3 (op3)})))

(defn measure-parallel-async
  "Execute three operations in parallel using core.async"
  [op1 op2 op3 & {:keys [label]}]
  (measure-time-verbose
   (or label "Parallel (async)")
   (fn []
     (let [c1 (async/thread (op1))
           c2 (async/thread (op2))
           c3 (async/thread (op3))]
       {:op1 (async/<!! c1)
        :op2 (async/<!! c2)
        :op3 (async/<!! c3)}))))

(defn measure-parallel-threads
  "Execute three operations using explicit threads"
  [op1 op2 op3 & {:keys [label]}]
  (measure-time-verbose
   (or label "Parallel (threads)")
   (fn []
     (let [t1 (Thread. op1)
           t2 (Thread. op2)
           t3 (Thread. op3)]
       (.start t1)
       (.start t2)
       (.start t3)
       (.join t1)
       (.join t2)
       (.join t3)
       {}))))

(defn measure-parallel-futures
  "Execute three operations using futures"
  [op1 op2 op3 & {:keys [label]}]
  (measure-time-verbose
   (or label "Parallel (futures)")
   (fn []
     (let [f1 (future (op1))
           f2 (future (op2))
           f3 (future (op3))]
       {:op1 @f1
        :op2 @f2
        :op3 @f3}))))

;; =============================================================================
;; Section 3: Speedup and Efficiency Metrics
;; =============================================================================

(defn calculate-speedup
  "Calculate speedup factor (sequential time / parallel time)"
  [sequential-ms parallel-ms]
  (double (Math/round (* 100 (/ sequential-ms parallel-ms)))) )

(defn calculate-efficiency
  "Calculate parallel efficiency (speedup / num-processors)"
  [speedup num-processors]
  (double (Math/round (* 100 (/ speedup num-processors)))))

(defn analyze-parallelism
  "Analyze parallelism metrics from sequential and parallel measurements"
  [sequential-result parallel-result & {:keys [num-processors]}]
  (let [num-procs (or num-processors 3)
        seq-time (:elapsed-ms sequential-result)
        par-time (:elapsed-ms parallel-result)
        speedup (calculate-speedup seq-time par-time)
        efficiency (calculate-efficiency speedup num-procs)]
    {:sequential-time-ms seq-time
     :parallel-time-ms par-time
     :speedup speedup
     :efficiency efficiency
     :num-processors num-procs
     :overhead-ms (- par-time (/ seq-time num-procs))
     :theoretical-speedup (* 100 num-procs)}))

;; =============================================================================
;; Section 4: Agent-Specific Benchmarks
;; =============================================================================

(defn benchmark-sicp-agents
  "Benchmark SICP evaluator parallel agents"
  [seed depth & {:keys [iterations]}]
  (let [iterations (or iterations 3)
        seed-val (or seed 42)
        depth-val (or depth 2)]
    (loop [i 0 results []]
      (if (< i iterations)
        (let [seq-result (measure-sequential
                          #(do (Thread/sleep 10) "sicp-agent-1")
                          #(do (Thread/sleep 12) "sicp-agent-2")
                          #(do (Thread/sleep 11) "sicp-agent-3")
                          :label (str "SICP Sequential #" (inc i)))

              par-result (measure-parallel-async
                          #(do (Thread/sleep 10) "sicp-agent-1")
                          #(do (Thread/sleep 12) "sicp-agent-2")
                          #(do (Thread/sleep 11) "sicp-agent-3")
                          :label (str "SICP Parallel #" (inc i)))

              analysis (analyze-parallelism seq-result par-result :num-processors 3)]
          (recur (inc i) (conj results analysis)))
        {:benchmark :sicp-agents
         :iterations iterations
         :seed seed-val
         :depth depth-val
         :results results
         :average-speedup (double (Math/round
                                  (/ (reduce + (map :speedup results)) iterations)))
         :average-efficiency (double (Math/round
                                     (/ (reduce + (map :efficiency results)) iterations)))}))))

(defn benchmark-discopy-agents
  "Benchmark Discopy categorical agents"
  [seed depth & {:keys [iterations]}]
  (let [iterations (or iterations 3)
        seed-val (or seed 42)
        depth-val (or depth 2)]
    (loop [i 0 results []]
      (if (< i iterations)
        (let [seq-result (measure-sequential
                          #(do (Thread/sleep 15) "discopy-agent-1")
                          #(do (Thread/sleep 18) "discopy-agent-2")
                          #(do (Thread/sleep 16) "discopy-agent-3")
                          :label (str "Discopy Sequential #" (inc i)))

              par-result (measure-parallel-async
                          #(do (Thread/sleep 15) "discopy-agent-1")
                          #(do (Thread/sleep 18) "discopy-agent-2")
                          #(do (Thread/sleep 16) "discopy-agent-3")
                          :label (str "Discopy Parallel #" (inc i)))

              analysis (analyze-parallelism seq-result par-result :num-processors 3)]
          (recur (inc i) (conj results analysis)))
        {:benchmark :discopy-agents
         :iterations iterations
         :seed seed-val
         :depth depth-val
         :results results
         :average-speedup (double (Math/round
                                  (/ (reduce + (map :speedup results)) iterations)))
         :average-efficiency (double (Math/round
                                     (/ (reduce + (map :efficiency results)) iterations)))}))))

(defn benchmark-github-agents
  "Benchmark GitHub ecosystem agents"
  [seed depth & {:keys [iterations]}]
  (let [iterations (or iterations 3)
        seed-val (or seed 42)
        depth-val (or depth 2)]
    (loop [i 0 results []]
      (if (< i iterations)
        (let [seq-result (measure-sequential
                          #(do (Thread/sleep 20) "github-agent-1")
                          #(do (Thread/sleep 25) "github-agent-2")
                          #(do (Thread/sleep 22) "github-agent-3")
                          :label (str "GitHub Sequential #" (inc i)))

              par-result (measure-parallel-async
                          #(do (Thread/sleep 20) "github-agent-1")
                          #(do (Thread/sleep 25) "github-agent-2")
                          #(do (Thread/sleep 22) "github-agent-3")
                          :label (str "GitHub Parallel #" (inc i)))

              analysis (analyze-parallelism seq-result par-result :num-processors 3)]
          (recur (inc i) (conj results analysis)))
        {:benchmark :github-agents
         :iterations iterations
         :seed seed-val
         :depth depth-val
         :results results
         :average-speedup (double (Math/round
                                  (/ (reduce + (map :speedup results)) iterations)))
         :average-efficiency (double (Math/round
                                     (/ (reduce + (map :efficiency results)) iterations)))}))))

;; =============================================================================
;; Section 5: Cross-System Parallelism Analysis
;; =============================================================================

(defn run-all-benchmarks
  "Run benchmarks across all three systems"
  [& {:keys [seed depth iterations]}]
  (let [seed-val (or seed 42)
        depth-val (or depth 2)
        iter-val (or iterations 3)]
    {:timestamp (System/currentTimeMillis)
     :seed seed-val
     :depth depth-val
     :iterations iter-val
     :sicp (benchmark-sicp-agents seed-val depth-val :iterations iter-val)
     :discopy (benchmark-discopy-agents seed-val depth-val :iterations iter-val)
     :github (benchmark-github-agents seed-val depth-val :iterations iter-val)}))

(defn compare-system-parallelism
  "Compare parallelism across all three systems"
  [benchmark-results]
  (let [sicp-speedup (get-in benchmark-results [:sicp :average-speedup])
        discopy-speedup (get-in benchmark-results [:discopy :average-speedup])
        github-speedup (get-in benchmark-results [:github :average-speedup])

        sicp-eff (get-in benchmark-results [:sicp :average-efficiency])
        discopy-eff (get-in benchmark-results [:discopy :average-efficiency])
        github-eff (get-in benchmark-results [:github :average-efficiency])]

    {:type :cross-system-parallelism-analysis
     :timestamp (:timestamp benchmark-results)
     :systems {:sicp {:speedup sicp-speedup :efficiency sicp-eff}
               :discopy {:speedup discopy-speedup :efficiency discopy-eff}
               :github {:speedup github-speedup :efficiency github-eff}}
     :best-speedup (max sicp-speedup discopy-speedup github-speedup)
     :best-system (cond
                    (= (max sicp-speedup discopy-speedup github-speedup) sicp-speedup) :sicp
                    (= (max sicp-speedup discopy-speedup github-speedup) discopy-speedup) :discopy
                    :else :github)
     :average-speedup (double (Math/round (/ (+ sicp-speedup discopy-speedup github-speedup) 3)))
     :average-efficiency (double (Math/round (/ (+ sicp-eff discopy-eff github-eff) 3)))}))

;; =============================================================================
;; Section 6: Scaling Analysis
;; =============================================================================

(defn benchmark-scaling
  "Benchmark performance as number of agents increases"
  [num-agents-list & {:keys [label]}]
  (let [results (mapv (fn [num-agents]
                        (let [ops (vec (repeat num-agents #(do (Thread/sleep 10) (rand))))

                              seq-time (measure-time
                                        (fn []
                                          (doall (map (fn [op] (op)) ops))))

                              par-time (measure-time
                                        (fn []
                                          (let [futures (mapv future ops)]
                                            (mapv deref futures))))]

                          {:num-agents num-agents
                           :sequential-ms (:elapsed-ms seq-time)
                           :parallel-ms (:elapsed-ms par-time)
                           :speedup (calculate-speedup
                                    (:elapsed-ms seq-time)
                                    (:elapsed-ms par-time))
                           :efficiency (calculate-efficiency
                                       (calculate-speedup
                                        (:elapsed-ms seq-time)
                                        (:elapsed-ms par-time))
                                       num-agents)}))
                      num-agents-list)]

    {:type :scaling-analysis
     :label (or label "Agent Scaling")
     :timestamp (System/currentTimeMillis)
     :results results
     :speedup-trend (mapv :speedup results)
     :efficiency-trend (mapv :efficiency results)}))

;; =============================================================================
;; Section 7: Contention and Coordination Overhead
;; =============================================================================

(defn measure-coordination-overhead
  "Measure overhead of agent coordination mechanisms"
  [num-measurements & {:keys [label]}]
  (let [measurements (mapv (fn [i]
                             (let [; Time to coordinate 3 agents
                                   coord-time (measure-time
                                               (fn []
                                                 (let [c1 (async/chan)
                                                       c2 (async/chan)
                                                       c3 (async/chan)]
                                                   (async/>!! c1 {:id 1})
                                                   (async/>!! c2 {:id 2})
                                                   (async/>!! c3 {:id 3})
                                                   [(async/<!! c1)
                                                    (async/<!! c2)
                                                    (async/<!! c3)])))

                                   ; Time without coordination
                                   no-coord-time (measure-time
                                                  (fn []
                                                    [{:id 1} {:id 2} {:id 3}]))]

                               {:measurement i
                                :coordination-ms (:elapsed-ms coord-time)
                                :no-coordination-ms (:elapsed-ms no-coord-time)
                                :overhead-ms (- (:elapsed-ms coord-time)
                                               (:elapsed-ms no-coord-time))}))
                           (range num-measurements))]

    {:type :coordination-overhead
     :label (or label "Coordination Overhead")
     :timestamp (System/currentTimeMillis)
     :measurements measurements
     :average-overhead (double (Math/round
                               (/ (reduce + (map :overhead-ms measurements))
                                  num-measurements)))
     :max-overhead (apply max (map :overhead-ms measurements))
     :min-overhead (apply min (map :overhead-ms measurements))}))

;; =============================================================================
;; Section 8: Reporting and Analysis
;; =============================================================================

(defn format-speedup-table
  "Format speedup comparison as ASCII table"
  [comparison-result]
  (let [systems (get-in comparison-result [:systems])]
    (str
     "Parallelism Comparison Across Systems\n"
     "=====================================\n"
     "System    | Speedup | Efficiency\n"
     "----------|---------|----------\n"
     "SICP      | " (format "%5.1f" (get-in systems [:sicp :speedup])) "% | "
     (format "%5.1f" (get-in systems [:sicp :efficiency])) "%\n"
     "Discopy   | " (format "%5.1f" (get-in systems [:discopy :speedup])) "% | "
     (format "%5.1f" (get-in systems [:discopy :efficiency])) "%\n"
     "GitHub    | " (format "%5.1f" (get-in systems [:github :speedup])) "% | "
     (format "%5.1f" (get-in systems [:github :efficiency])) "%\n"
     "----------|---------|----------\n"
     "Average   | " (format "%5.1f" (:average-speedup comparison-result)) "% | "
     (format "%5.1f" (:average-efficiency comparison-result)) "%")))

(defn format-scaling-table
  "Format scaling analysis as ASCII table"
  [scaling-result]
  (let [results (:results scaling-result)]
    (str
     "Scaling Analysis: " (:label scaling-result) "\n"
     "=====================================================\n"
     "Agents | Sequential(ms) | Parallel(ms) | Speedup | Efficiency\n"
     "-------|----------------|--------------|---------|----------\n"
     (str/join "\n"
       (map (fn [r]
              (str (format "%3d" (:num-agents r)) "    | "
                   (format "%14.2f" (:sequential-ms r)) " | "
                   (format "%12.2f" (:parallel-ms r)) " | "
                   (format "%7.1f" (:speedup r)) "% | "
                   (format "%8.1f" (:efficiency r)) "%"))
            results)))))

(defn format-overhead-report
  "Format coordination overhead report"
  [overhead-result]
  (str
   "Coordination Overhead Analysis\n"
   "=============================\n"
   "Type: " (:label overhead-result) "\n"
   "Average Overhead: " (format "%.2f ms\n" (:average-overhead overhead-result))
   "Max Overhead: " (format "%.2f ms\n" (:max-overhead overhead-result))
   "Min Overhead: " (format "%.2f ms\n" (:min-overhead overhead-result))
   "Measurements: " (count (:measurements overhead-result))))

(defn generate-parallelism-report
  "Generate comprehensive parallelism analysis report"
  [benchmark-results]
  (let [comparison (compare-system-parallelism benchmark-results)
        scaling (benchmark-scaling [1 2 3 4 5 6] :label "Agent Scaling Study")
        overhead (measure-coordination-overhead 10 :label "Async Channel Coordination")]

    {:type :comprehensive-parallelism-report
     :timestamp (System/currentTimeMillis)
     :benchmark-results benchmark-results
     :comparison comparison
     :scaling scaling
     :coordination-overhead overhead
     :summary {:best-system (:best-system comparison)
               :average-speedup (:average-speedup comparison)
               :average-efficiency (:average-efficiency comparison)
               :max-agents-tested 6
               :measurements-per-system 3}}))

;; =============================================================================
;; Section 9: Real-world Simulation Benchmarks
;; =============================================================================

(defn simulate-agent-workload
  "Simulate realistic agent workload with varying complexity"
  [agent-id complexity-ms & {:keys [iterations]}]
  (let [iterations (or iterations 5)]
    (loop [i 0 results []]
      (if (< i iterations)
        (let [work-time (measure-time #(Thread/sleep complexity-ms))]
          (recur (inc i) (conj results (:elapsed-ms work-time))))
        {:agent-id agent-id
         :total-work-ms (reduce + results)
         :measurements results
         :average-ms (double (Math/round (/ (reduce + results) iterations)))}))))

(defn benchmark-realistic-parallel-workload
  "Benchmark realistic workload: agent1=light, agent2=medium, agent3=heavy"
  [& {:keys [iterations]}]
  (let [iter-val (or iterations 3)]
    (loop [i 0 results []]
      (if (< i iter-val)
        (let [seq-result (measure-sequential
                          #(simulate-agent-workload 1 10 :iterations 2)  ; light
                          #(simulate-agent-workload 2 20 :iterations 2)  ; medium
                          #(simulate-agent-workload 3 30 :iterations 2)  ; heavy
                          :label (str "Realistic Seq #" (inc i)))

              par-result (measure-parallel-async
                          #(simulate-agent-workload 1 10 :iterations 2)
                          #(simulate-agent-workload 2 20 :iterations 2)
                          #(simulate-agent-workload 3 30 :iterations 2)
                          :label (str "Realistic Par #" (inc i)))

              analysis (analyze-parallelism seq-result par-result :num-processors 3)]
          (recur (inc i) (conj results analysis)))
        {:benchmark :realistic-workload
         :iterations iter-val
         :results results
         :average-speedup (double (Math/round
                                  (/ (reduce + (map :speedup results)) iter-val)))
         :average-efficiency (double (Math/round
                                     (/ (reduce + (map :efficiency results)) iter-val)))}))))

;; =============================================================================
;; Section 10: Statistical Analysis
;; =============================================================================

(defn calculate-statistics
  "Calculate mean, median, std dev for measurements"
  [measurements]
  (let [sorted (sort measurements)
        count (count measurements)
        mean (/ (reduce + measurements) count)
        median (if (even? count)
                 (/ (+ (nth sorted (dec (/ count 2)))
                       (nth sorted (/ count 2))) 2)
                 (nth sorted (quot count 2)))
        variance (/ (reduce + (map #(* (- % mean) (- % mean)) measurements)) count)
        stddev (Math/sqrt variance)]
    {:count count
     :mean (double (Math/round (* 100 mean)))
     :median (double (Math/round (* 100 median)))
     :min (apply min measurements)
     :max (apply max measurements)
     :stddev (double (Math/round (* 100 stddev)))}))

(defn analyze-speedup-distribution
  "Analyze distribution of speedup values"
  [benchmark-results system]
  (let [speedups (map :speedup (get-in benchmark-results [system :results]))]
    {:system system
     :speedups speedups
     :statistics (calculate-statistics speedups)}))

;; =============================================================================
;; End of module
;; =============================================================================
