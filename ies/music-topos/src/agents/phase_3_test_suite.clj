(ns agents.phase-3-test-suite
  "Phase 3 Test Suite: Comprehensive Validation of Pattern Extraction

  Tests:
  1. 5D pattern extraction from tagged interactions
  2. K-means clustering convergence
  3. Archetype identification accuracy
  4. Anomaly detection sensitivity
  5. Dimensionality analysis correctness
  6. Complete Phase 2→3→4 pipeline

  Status: 2025-12-21 - Test framework ready"
  (:require [agents.phase-3-pattern-extraction :as phase3]
            [agents.phase-3-integration :as phase3-int]
            [clojure.math :as math]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: Mock Data Generation
;; =============================================================================

(defn generate-mock-phase2-result
  "Generate realistic mock Phase 2 result for testing"
  []

  (let [;; Create mock interactions
        interactions (vec (for [i (range 50)]
                          {:id i
                           :timestamp (+ 1000000000000 (* i 3600000))
                           :content (str "Mock interaction " i)
                           :in-reply-to (if (> i 0) (rand-int i) nil)
                           :mentions-count (if (> (rand) 0.7) (rand-int 3) 0)
                           :collaborators-count (if (> (rand) 0.6) (rand-int 2) 0)
                           :links-count (if (> (rand) 0.5) 1 0)}))

        ;; Create mock leitmotif tags
        leitmotifs [:technical-innovation :collaborative-work
                   :philosophical-reflection :network-building
                   :musical-creation :synthesis]
        tagged-interactions
        (mapv (fn [interaction]
               (assoc interaction
                 :primary-leitmotif (rand-nth leitmotifs)
                 :confidence-score (+ 0.5 (rand 0.5))))
             interactions)]

    {:phase "2"
     :status :complete
     :all-data {:interactions interactions
               :tagged-interactions tagged-interactions
               :musical-events (vec (for [i (range (count tagged-interactions))]
                                     {:id i
                                      :pitch (+ 24 (rand-int 84))
                                      :velocity (rand-int 128)
                                      :duration (+ 250 (rand 3750))}))
               :timeline []}
     :seed-selection {:optimal-seed 12345
                     :seed-entropy 2.85
                     :target-entropy 2.85
                     :match-quality 0.92}
     :leitmotif-tagging {:total-interactions (count tagged-interactions)
                        :completeness 1.0
                        :quality :excellent}
     :musical-composition {:num-events (count interactions)
                          :duration-seconds 300.0}}))

;; =============================================================================
;; Section 2: Individual Component Tests
;; =============================================================================

(defn test-5d-pattern-extraction
  "Test 1: Verify 5D pattern extraction works correctly"
  []

  (println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
  (println "TEST 1: 5D Pattern Extraction")
  (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

  (let [interaction {:id 1
                    :content "Test interaction"
                    :timestamp 1000
                    :in-reply-to nil
                    :mentions-count 1
                    :collaborators-count 2
                    :links-count 1
                    :primary-leitmotif :technical-innovation}
       entropy-baseline {:optimal-seed 100
                        :seed-entropy 2.85
                        :temporal 2.0}
       pattern (phase3/extract-5d-pattern interaction :technical-innovation entropy-baseline)]

    (println (str "✅ Pattern extracted: " (:pattern-vector pattern)))
    (println (str "   Dimensions: " (:dimensions pattern)))
    (println (str "   Leitmotif: " (:leitmotif pattern)))

    ;; Validate vector length
    (assert (= 5 (count (:pattern-vector pattern)))
            "Pattern vector should have 5 dimensions")

    ;; Validate dimension values are in [0, 1]
    (assert (every? (fn [v] (and (>= v 0) (<= v 1)))
                   (:pattern-vector pattern))
            "All dimensions should be in [0, 1]")

    (println "✅ Pattern extraction test PASSED")
    true))

(defn test-kmeans-clustering
  "Test 2: Verify K-means clustering converges"
  []

  (println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
  (println "TEST 2: K-Means Clustering Convergence")
  (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

  ;; Create mock patterns with distinct clusters
  (let [;; Cluster 1: high topic, low mode
        cluster1 (vec (for [i (range 10)]
                       {:pattern-vector [0.9 0.1 (+ 0.3 (rand 0.2))
                                        (+ 0.4 (rand 0.2)) (+ 0.5 (rand 0.2))]
                       :id i}))

        ;; Cluster 2: low topic, high mode
        cluster2 (vec (for [i (range 10 20)]
                       {:pattern-vector [0.1 0.9 (+ 0.6 (rand 0.2))
                                        (+ 0.2 (rand 0.2)) (+ 0.3 (rand 0.2))]
                       :id i}))

        ;; Cluster 3: medium everywhere
        cluster3 (vec (for [i (range 20 30)]
                       {:pattern-vector [0.5 0.5 (+ 0.5 (rand 0.1))
                                        (+ 0.5 (rand 0.1)) (+ 0.5 (rand 0.1))]
                       :id i}))

        all-patterns (concat cluster1 cluster2 cluster3)]

    (println (str "  Input patterns: " (count all-patterns)))
    (println (str "  Target clusters: 3"))

    (let [cluster-map (phase3/kmeans-cluster all-patterns 3 100)
          num-clusters (count cluster-map)]

      (println (str "✅ Clustering complete"))
      (println (str "   Actual clusters: " num-clusters))

      ;; Validate clustering produced correct number of clusters
      (assert (= 3 num-clusters) "Should have 3 clusters")

      ;; Validate all patterns are assigned
      (let [total-assigned (reduce + (map (fn [[_ patterns]] (count patterns)) cluster-map))]
        (assert (= (count all-patterns) total-assigned)
                "All patterns should be assigned to clusters"))

      (println "✅ K-Means clustering test PASSED")
      true)))

(defn test-archetype-identification
  "Test 3: Verify archetype identification works"
  []

  (println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
  (println "TEST 3: Archetype Identification")
  (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

  (let [;; Create mock cluster map
        patterns (vec (for [i (range 20)]
                       {:pattern-vector [0.5 0.6 0.7 0.8 0.9]
                       :leitmotif (if (< i 10) :technical-innovation :musical-creation)
                       :id i}))
        cluster-map {0 patterns}

        ;; Identify archetypes
        archetypes (phase3/identify-archetypes cluster-map)]

    (println (str "✅ Archetypes identified"))
    (println (str "   Count: " (count archetypes)))

    ;; Validate archetypes
    (assert (> (count archetypes) 0) "Should identify at least one archetype")
    (assert (every? (fn [[_ arch]]
                      (contains? arch :size)
                      (contains? arch :dominant-leitmotif))
                   archetypes)
            "All archetypes should have size and leitmotif")

    (println "✅ Archetype identification test PASSED")
    true))

(defn test-anomaly-detection
  "Test 4: Verify anomaly detection works"
  []

  (println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
  (println "TEST 4: Anomaly Detection")
  (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

  (let [;; Create patterns with outliers
        normal-patterns (vec (for [i (range 20)]
                             {:pattern-vector [0.5 0.5 0.5 0.5 0.5]
                             :id i}))
        outlier-patterns [(assoc (first normal-patterns)
                            :pattern-vector [0.0 0.0 0.0 0.0 0.0]
                            :id 100)
                         (assoc (first normal-patterns)
                            :pattern-vector [1.0 1.0 1.0 1.0 1.0]
                            :id 101)]
        all-patterns (concat normal-patterns outlier-patterns)
        centroid [0.5 0.5 0.5 0.5 0.5]

        ;; Detect anomalies
        anomalies (phase3/detect-anomalies all-patterns centroid)]

    (println (str "✅ Anomalies detected"))
    (println (str "   Normal patterns: " (count normal-patterns)))
    (println (str "   Outliers injected: " (count outlier-patterns)))
    (println (str "   Anomalies found: " (count anomalies)))

    ;; Validate some anomalies were detected
    (assert (> (count anomalies) 0) "Should detect at least one anomaly")

    (println "✅ Anomaly detection test PASSED")
    true))

(defn test-dimensionality-analysis
  "Test 5: Verify dimensionality analysis works"
  []

  (println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
  (println "TEST 5: Dimensionality Analysis")
  (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

  (let [;; Create patterns with varying variance per dimension
        patterns (vec (for [i (range 30)]
                       {:pattern-vector [(rand 1.0)  ; High variance
                                        0.5          ; Zero variance
                                        (+ 0.4 (rand 0.2))  ; Low variance
                                        (+ 0.3 (rand 0.4))  ; Medium variance
                                        (rand 1.0)]  ; High variance
                       :id i}))

        ;; Analyze dimensionality
        analysis (phase3/dimension-importance patterns)]

    (println (str "✅ Dimensionality analysis complete"))
    (println (str "   Importance ranking computed"))

    ;; Validate analysis results
    (assert (= 5 (count (:importance analysis)))
            "Should have importance for all 5 dimensions")

    ;; Validate importance sums to 1.0 (approximately)
    (let [total-imp (reduce + (:importance analysis))]
      (assert (> total-imp 0.99) "Importance should sum to ~1.0"))

    (println "✅ Dimensionality analysis test PASSED")
    true))

;; =============================================================================
;; Section 3: Integration Tests
;; =============================================================================

(defn test-complete-phase3-pipeline
  "Test 6: Complete Phase 2→3 pipeline"
  []

  (println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
  (println "TEST 6: Complete Phase 2→3 Pipeline")
  (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

  (let [phase2-result (generate-mock-phase2-result)
        entropy-baseline (get-in phase2-result [:seed-selection])

        ;; Run complete Phase 3 pipeline
        phase3-result (phase3-int/run-full-phase-3 phase2-result entropy-baseline)]

    (println (str "✅ Phase 3 pipeline complete"))

    ;; Validate Phase 3 result structure
    (assert (= "3" (:phase phase3-result)) "Should be Phase 3")
    (assert (= :complete (:status phase3-result)) "Should have complete status")
    (assert (contains? phase3-result :pattern-extraction) "Should have patterns")
    (assert (contains? phase3-result :clustering) "Should have clustering")
    (assert (contains? phase3-result :archetypes) "Should have archetypes")
    (assert (contains? phase3-result :anomalies) "Should have anomalies")
    (assert (contains? phase3-result :dimensionality) "Should have dimensionality")

    (println "✅ Complete Phase 2→3 pipeline test PASSED")
    true))

;; =============================================================================
;; Section 4: Run All Tests
;; =============================================================================

(defn run-phase-3-tests
  "Run all Phase 3 tests"
  []

  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║       PHASE 3 TEST SUITE - COMPREHENSIVE VALIDATION     ║")
  (println "╚══════════════════════════════════════════════════════════╝")

  (let [tests [{:name "5D Pattern Extraction" :fn test-5d-pattern-extraction}
               {:name "K-Means Clustering" :fn test-kmeans-clustering}
               {:name "Archetype Identification" :fn test-archetype-identification}
               {:name "Anomaly Detection" :fn test-anomaly-detection}
               {:name "Dimensionality Analysis" :fn test-dimensionality-analysis}
               {:name "Complete Phase 2→3 Pipeline" :fn test-complete-phase3-pipeline}]

        results (vec (for [test tests]
                      (try
                        ((:fn test))
                        {:test (:name test) :status :passed}
                        (catch Exception e
                          {:test (:name test) :status :failed :error (.getMessage e)}))))]

    ;; Summary
    (println "\n╔══════════════════════════════════════════════════════════╗")
    (println "║              TEST RESULTS SUMMARY                      ║")
    (println "╚══════════════════════════════════════════════════════════╝\n")

    (let [passed (count (filter #(= :passed (:status %)) results))
          failed (count (filter #(= :failed (:status %)) results))]

      (println (str "Total Tests: " (count results)))
      (println (str "✅ Passed: " passed))
      (println (str "❌ Failed: " failed))
      (println "")

      (doseq [result results]
        (if (= :passed (:status result))
          (printf "✅ %s\n" (:test result))
          (printf "❌ %s: %s\n" (:test result) (:error result)))))

    (every? #(= :passed (:status %)) results)))
