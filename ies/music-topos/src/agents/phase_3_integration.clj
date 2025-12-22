(ns agents.phase-3-integration
  "Phase 3 Integration: Complete Phase 2→3 Pattern Extraction Pipeline

  Orchestrates the full flow:
  1. Takes Phase 2 result (interactions, leitmotif tags, musical composition)
  2. Runs Phase 3 pattern extraction (5D analysis)
  3. Performs K-means clustering on 5D vectors
  4. Identifies archetypes and anomalies
  5. Generates dimensionality reduction insights
  6. Prepares output for Phase 4 (agent-o-rama training)

  Status: 2025-12-21 - Phase 2→3 transition ready"
  (:require [agents.phase-3-pattern-extraction :as phase3]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: Complete Phase 2→3 Pipeline
;; =============================================================================

(defn run-full-phase-3
  "Execute complete Phase 2→3 transition
   Input: Phase 2 result map with tagged interactions
   Output: Phase 3 pattern clusters, archetypes, anomalies"
  [phase-2-result entropy-baseline]

  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║    PHASE 3: COMPLETE 5D PATTERN EXTRACTION             ║")
  (println "║         (Phase 2→3 Integration Pipeline)                ║")
  (println "╚══════════════════════════════════════════════════════════╝")

  ;; Execute Phase 3 core pipeline
  (let [phase-3-result (phase3/run-phase-3 phase-2-result)]

    ;; Generate summary report
    (print-phase-3-summary phase-3-result)

    phase-3-result))

;; =============================================================================
;; Section 2: Summary and Reporting
;; =============================================================================

(defn print-phase-3-summary
  "Print comprehensive Phase 3 summary"
  [phase-3-result]

  (let [patterns (count (get-in phase-3-result [:pattern-extraction :sample-patterns]))
        num-clusters (get-in phase-3-result [:clustering :num-clusters])
        num-archetypes (count (get-in phase-3-result [:archetypes]))
        num-anomalies (get-in phase-3-result [:anomalies :total-anomalies])
        dimension-names [:topic :mode :temporal :network :length]
        importance (get-in phase-3-result [:dimensionality :importance])]

    (println "\n╔══════════════════════════════════════════════════════════╗")
    (println "║       PHASE 3 INTEGRATION COMPLETE - SUMMARY             ║")
    (println "╚══════════════════════════════════════════════════════════╝\n")

    (println "📊 PATTERN EXTRACTION RESULTS")
    (println "─────────────────────────────────────────────────────────")
    (println (str "  Total patterns extracted: "
                 (get-in phase-3-result [:pattern-extraction :total-patterns])))
    (println "")

    (println "🔀 CLUSTERING ANALYSIS")
    (println "─────────────────────────────────────────────────────────")
    (println (str "  Number of clusters: " num-clusters))
    (doseq [[cluster-id size]
            (get-in phase-3-result [:clustering :cluster-sizes])]
      (printf "    Cluster %d: %d patterns\n" cluster-id size))
    (println "")

    (println "🎭 ARCHETYPE IDENTIFICATION")
    (println "─────────────────────────────────────────────────────────")
    (println (str "  Archetypes identified: " num-archetypes))
    (doseq [[name archetype] (sort-by key (get-in phase-3-result [:archetypes]))]
      (printf "    %s: %d patterns\n" name (:size archetype)))
    (println "")

    (println "⚠️  ANOMALY DETECTION")
    (println "─────────────────────────────────────────────────────────")
    (println (str "  Anomalies detected: " num-anomalies))
    (println "")

    (println "📐 DIMENSIONALITY IMPORTANCE RANKING")
    (println "─────────────────────────────────────────────────────────")
    (let [ranked (map vector dimension-names importance)
          sorted-dims (sort-by (comp - second) ranked)]
      (doseq [[dim imp] sorted-dims]
        (printf "  %s: %.1f%%\n" (str/upper-case (str dim)) (* 100 imp))))
    (println "")))

;; =============================================================================
;; Section 3: Prepare for Phase 4 (Agent Training)
;; =============================================================================

(defn prepare-training-data-for-phase4
  "Extract training data from Phase 3 for Phase 4 agent learning
   Returns map of archetype-specific training sets"
  [phase-3-result]

  (println "\n🧠 Preparing Training Data for Phase 4 (Agent-O-Rama)")
  (println "─────────────────────────────────────────────────────────")

  (let [archetypes (get-in phase-3-result [:archetypes])
        all-patterns (get-in phase-3-result [:all-data :patterns])
        cluster-map (get-in phase-3-result [:all-data :full-cluster-map])

        ;; Build training sets per archetype
        training-data (reduce (fn [acc [archetype-name archetype]]
                               (let [cluster-id (:cluster-id archetype)
                                     cluster-patterns (get cluster-map cluster-id)
                                     training-set {:archetype-name archetype-name
                                                  :leitmotif (:dominant-leitmotif archetype)
                                                  :num-examples (count cluster-patterns)
                                                  :characteristic-dims (:dimension-means archetype)
                                                  :patterns cluster-patterns}]

                                 (assoc acc archetype-name training-set)))
                             {}
                             archetypes)]

    (println (str "✅ Prepared " (count training-data) " training sets (one per archetype)"))
    (doseq [[name dataset] (sort-by key training-data)]
      (printf "  %s: %d examples\n" name (:num-examples dataset)))
    (println "")

    training-data))

;; =============================================================================
;; Section 4: Export Phase 3 Results
;; =============================================================================

(defn export-phase-3-checkpoint
  "Export Phase 3 results as EDN checkpoint for Phase 4"
  [phase-3-result export-path]

  (println "\n💾 EXPORTING PHASE 3 CHECKPOINT")
  (println "─────────────────────────────────────────────────────────")
  (println (str "  Export path: " export-path))

  ;; Create comprehensive checkpoint
  (let [checkpoint {:phase "3"
                   :timestamp (java.util.Date.)
                   :pattern-extraction (get phase-3-result :pattern-extraction)
                   :clustering (dissoc (get phase-3-result :clustering)
                                      :clusters-map)  ; Avoid huge data
                   :archetypes (get phase-3-result :archetypes)
                   :anomalies {:total (get-in phase-3-result [:anomalies :total-anomalies])
                              :by-cluster (get-in phase-3-result [:anomalies :anomalies-by-cluster])}
                   :dimensionality (get phase-3-result :dimensionality)}]

    (try
      (spit export-path (pr-str checkpoint))
      (println (str "✅ Phase 3 checkpoint saved (" (count (pr-str checkpoint)) " bytes)"))
      (println "")
      true
      (catch Exception e
        (println (str "❌ Export failed: " (.getMessage e)))
        false))))

(defn export-phase-3-summary
  "Export human-readable summary of Phase 3"
  [phase-3-result export-path]

  (println "\n📄 EXPORTING PHASE 3 SUMMARY")
  (println "─────────────────────────────────────────────────────────")
  (println (str "  Export path: " export-path))

  (let [summary-content
        (str/join "\n"
                 ["═════════════════════════════════════════════════════════"
                  "PHASE 3: 5D PATTERN EXTRACTION & ANALYSIS REPORT"
                  (str "Generated: " (java.util.Date.))
                  "═════════════════════════════════════════════════════════\n"

                  "PATTERN EXTRACTION"
                  "─────────────────────────────────────────────────────────"
                  (str "Total patterns extracted: "
                       (get-in phase-3-result [:pattern-extraction :total-patterns]))
                  ""

                  "CLUSTERING RESULTS"
                  "─────────────────────────────────────────────────────────"
                  (str "Number of clusters: " (get-in phase-3-result [:clustering :num-clusters]))
                  (str/join "\n"
                           (for [[cluster-id size]
                                 (get-in phase-3-result [:clustering :cluster-sizes])]
                             (str "  Cluster " cluster-id ": " size " patterns")))
                  ""

                  "IDENTIFIED ARCHETYPES"
                  "─────────────────────────────────────────────────────────"
                  (str "Total archetypes: " (count (get-in phase-3-result [:archetypes])))
                  (str/join "\n"
                           (for [[name archetype]
                                 (sort-by key (get-in phase-3-result [:archetypes]))]
                             (str "  " name
                                  ": " (:size archetype) " patterns, "
                                  "dominant=" (name (:dominant-leitmotif archetype)))))
                  ""

                  "ANOMALY DETECTION"
                  "─────────────────────────────────────────────────────────"
                  (str "Total anomalies: " (get-in phase-3-result [:anomalies :total-anomalies]))
                  ""

                  "DIMENSIONALITY ANALYSIS"
                  "─────────────────────────────────────────────────────────"
                  (str/join "\n"
                           (for [[dim imp]
                                 (map vector
                                      [:topic :mode :temporal :network :length]
                                      (get-in phase-3-result [:dimensionality :importance]))]
                             (str "  " (str/upper-case (str dim))
                                  ": " (format "%.1f%%" (* 100 imp)))))
                  ""

                  "NEXT PHASE (Phase 4)"
                  "─────────────────────────────────────────────────────────"
                  "Phase 4 will train agent-o-rama using these patterns as:"
                  "  - Training examples for each archetype"
                  "  - Entropy baselines for diversity monitoring"
                  "  - Anomaly profiles for novelty detection"
                  ""])]

    (try
      (spit export-path summary-content)
      (println (str "✅ Summary exported"))
      (println "")
      true
      (catch Exception e
        (println (str "❌ Export failed: " (.getMessage e)))
        false))))

;; =============================================================================
;; Section 5: Phase 3 Complete Handler
;; =============================================================================

(defn phase-3-complete
  "Mark Phase 3 completion and prepare for Phase 4
   Returns comprehensive Phase 3 results + Phase 4 prep data"
  [phase-3-result
   {:keys [export-checkpoint-path export-summary-path]
    :or {export-checkpoint-path nil
         export-summary-path nil}}]

  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║    PHASE 3 PROCESSING COMPLETE - PREPARING PHASE 4     ║")
  (println "╚══════════════════════════════════════════════════════════╝")

  ;; Export results if paths provided
  (when export-checkpoint-path
    (export-phase-3-checkpoint phase-3-result export-checkpoint-path))

  (when export-summary-path
    (export-phase-3-summary phase-3-result export-summary-path))

  ;; Prepare training data for Phase 4
  (let [training-data (prepare-training-data-for-phase4 phase-3-result)]

    (println "\n╔══════════════════════════════════════════════════════════╗")
    (println "║              PHASE 3 STATUS: COMPLETE ✅               ║")
    (println "║           Ready to transition to Phase 4               ║")
    (println "╚══════════════════════════════════════════════════════════╝\n")

    {:phase-3-result phase-3-result
     :phase-4-training-data training-data
     :status :complete
     :message "Phase 3 complete. Phase 4 (agent-o-rama training) ready to begin."}))
