(ns agents.phase-2-integration
  "Phase 2 Integration: Complete Optimal Seed → Leitmotif → Colorable Music Pipeline

  Integrates:
  1. Optimal seed selection (entropy matching)
  2. Leitmotif recognition (pattern extraction)
  3. Colorable music topos (color+sound synthesis)

  Complete data flow:
  Phase 1 Data (interactions)
    → Entropy baseline
    → Optimal Gay seed selection
    → Leitmotif tagging + color assignment
    → Colorable music events
    → SuperCollider synthesis code
    → Realizable possible worlds

  Status: 2025-12-21 - Phase 1→2 transition ready"
  (:require [agents.optimal-seed-selection :as seed]
            [agents.leitmotif-recognition :as leitmotif]
            [agents.colorable-music-topos :as music]
            [agents.entropy-metrics :as entropy]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: Pipeline Orchestration
;; =============================================================================

(defn phase-2-complete-pipeline
  "Complete Phase 1→2 transition:
   Raw interactions → Optimal seed → Leitmotifs → Colors → Music"
  [interactions interaction-entropy-baseline]

  (println "\\n╔══════════════════════════════════════════════════════════╗")
  (println "║          PHASE 2: COMPLETE INTEGRATION PIPELINE           ║")
  (println "╚══════════════════════════════════════════════════════════╝\\n")

  ;; Step 1: Select optimal seed from interaction entropy
  (println \"📊 STEP 1: Optimal Seed Selection\")
  (println \"─────────────────────────────────────────────────────────\")

  (let [seed-result (seed/select-optimal-initial-seed interaction-entropy-baseline)
        optimal-seed (:optimal-seed seed-result)]

    (println (str \"  Selected seed: \" optimal-seed))
    (println (str \"  Target entropy: \" (format \"%.2f\" (:target-entropy seed-result)) \" bits\"))
    (println (str \"  Achieved entropy: \" (format \"%.2f\" (:entropy seed-result)) \" bits\"))
    (println (str \"  Match quality: \" (format \"%.1f%%\" (* 100 (:match-quality seed-result)))))
    (println \"\")

    ;; Step 2: Tag interactions with leitmotifs
    (println \"🎭 STEP 2: Leitmotif Recognition & Tagging\")
    (println \"─────────────────────────────────────────────────────────\")

    (let [tagged-interactions (leitmotif/tag-interactions-with-leitmotifs interactions)
          leitmotif-validation (leitmotif/validate-leitmotif-tagging tagged-interactions)
          leitmotif-dist (leitmotif/leitmotif-distribution tagged-interactions)]

      (println (str \"  Total interactions: \" (:total-tagged leitmotif-validation)))
      (println (str \"  Tagged completeness: \" (format \"%.1f%%\" (* 100 (:completeness leitmotif-validation)))))
      (println (str \"  Average confidence score: \" (format \"%.2f\" (:avg-primary-score leitmotif-validation))))
      (println (str \"  Quality rating: \" (str/upper-case (str (:quality leitmotif-validation)))))
      (println \"  Distribution:\")(doseq [[lm data] leitmotif-dist]
        (printf \"    %s: %d (%.1f%%)\\n\"
               (str/replace (str lm) #\":\" \"\")
               (:count data)
               (* 100 (:proportion data))))
      (println \"\")

      ;; Step 3: Convert to colorable musical events
      (println \"🎨 STEP 3: Color Mapping\")
      (println \"─────────────────────────────────────────────────────────\")

      (let [musical-events (music/interactions-to-musical-sequence
                           interactions optimal-seed tagged-interactions)]

        (println (str \"  Total musical events: \" (count musical-events)))
        (println (str \"  Hue range: 0-360° (full spectrum)\"))
        (println (str \"  Pitch range: C1 (MIDI 24) to B8 (MIDI 107)\"))
        (println (str \"  Velocity range: 0-127 (by saturation)\"))
        (println \"\")

        ;; Step 4: Arrange on timeline with temporal organization
        (println \"⏱️  STEP 4: Timeline Arrangement\")
        (println \"─────────────────────────────────────────────────────────\")

        (let [timeline (music/sequence-to-timeline musical-events)
              duration-seconds (if (empty? timeline)
                                0
                                (apply max (map :offset-seconds timeline)))]

          (println (str \"  Timeline duration: \" (format \"%.1f\" duration-seconds) \" seconds\"))
          (if (> (count timeline) 0)
            (println (str \"  First event: \" (format \"%.3f\" (:offset-seconds (first timeline))) \"s\"))
            (println \"  (No events)\"))
          (if (> (count timeline) 0)
            (println (str \"  Last event: \" (format \"%.3f\" (apply max (map :offset-seconds timeline))) \"s\"))
            (println \"  (No events)\"))
          (println \"\")

          ;; Step 5: Generate SuperCollider synthesis code
          (println \"🎵 STEP 5: SuperCollider Code Generation\")
          (println \"─────────────────────────────────────────────────────────\")

          (let [sc-code (music/generate-supercollider-code timeline)
                sc-lines (str/split sc-code #\"\\n\")]

            (println (str \"  Total lines of SC code: \" (count sc-lines)))
            (println (str \"  Sample (first 3 lines):\"))
            (doseq [line (take 3 sc-lines)]
              (println (str \"    \" line)))
            (if (> (count sc-lines) 3)
              (println (str \"    ... (\" (- (count sc-lines) 3) \" more lines)\")))
            (println \"\")

            ;; Return complete result
            {:phase \"2\"
             :status :complete
             :seed-selection {:optimal-seed optimal-seed
                             :seed-entropy (:entropy seed-result)
                             :target-entropy (:target-entropy seed-result)
                             :match-quality (:match-quality seed-result)}

             :leitmotif-tagging {:total-interactions (:total-tagged leitmotif-validation)
                                :completeness (:completeness leitmotif-validation)
                                :quality (:quality leitmotif-validation)
                                :distribution leitmotif-dist}

             :musical-composition {:num-events (count musical-events)
                                  :duration-seconds duration-seconds
                                  :events timeline}

             :supercollider {:code sc-code
                           :lines (count sc-lines)}

             :all-data {:interactions interactions
                       :tagged-interactions tagged-interactions
                       :musical-events musical-events
                       :timeline timeline
                       :supercollider-code sc-code}}))))

;; =============================================================================
;; Section 2: Summary Display
;; =============================================================================

(defn display-phase-2-summary
  "Display comprehensive Phase 2 summary"
  [result]
  (println \"\\n╔══════════════════════════════════════════════════════════╗\")
  (println \"║       PHASE 2 INTEGRATION COMPLETE - SUMMARY             ║\")
  (println \"╚══════════════════════════════════════════════════════════╝\\n\")

  (println \"🎯 KEY METRICS:\")
  (let [seed (:seed-selection result)
        leitmotif (:leitmotif-tagging result)
        music (:musical-composition result)
        sc (:supercollider result)]

    (println (str \"  Optimal Seed: \" (:optimal-seed seed)))
    (println (str \"  Seed Entropy: \" (format \"%.2f\" (:seed-entropy seed)) \" bits\"))
    (println (str \"  Entropy Match: \" (format \"%.1f%%\" (* 100 (:match-quality seed)))))
    (println \"\")

    (println (str \"  Total Interactions: \" (:total-interactions leitmotif)))
    (println (str \"  Leitmotif Tagging Completeness: \" (format \"%.1f%%\" (* 100 (:completeness leitmotif)))))
    (println (str \"  Tagging Quality: \" (str/upper-case (str (:quality leitmotif)))))
    (println \"\")

    (println (str \"  Musical Events Generated: \" (:num-events music)))
    (println (str \"  Total Duration: \" (format \"%.1f\" (:duration-seconds music)) \" seconds\"))
    (println (str \"  SuperCollider Code: \" (:lines sc) \" lines\"))
    (println \"\"))

  (println \"✅ PHASE 2 STATUS: COMPLETE\")
  (println \"\")
  (println \"Next steps:\")
  (println \"  1. Execute SuperCollider code for audio synthesis\")
  (println \"  2. Proceed to Phase 3: Extract 5D patterns from interactions\")
  (println \"  3. Phase 4: Train agent-o-rama with entropy monitoring\")
  (println \"\"))

;; =============================================================================
;; Section 3: Verification & Validation
;; =============================================================================

(defn verify-phase-2-output
  "Verify that Phase 2 output meets quality standards"
  [result]
  (let [seed (:seed-selection result)
        leitmotif (:leitmotif-tagging result)
        music (:musical-composition result)

        seed-match-ok? (>= (:match-quality seed) 0.9)
        tagging-complete? (>= (:completeness leitmotif) 0.95)
        music-generated? (> (:num-events music) 0)
        quality-acceptable? (#{:good :excellent} (:quality leitmotif))]

    {:seed-match-ok seed-match-ok?
     :tagging-complete tagging-complete?
     :music-generated music-generated?
     :quality-acceptable quality-acceptable?

     :all-checks-pass (and seed-match-ok?
                           tagging-complete?
                           music-generated?
                           quality-acceptable?)

     :status (if (and seed-match-ok? tagging-complete? music-generated? quality-acceptable?)
             :pass
             :fail-see-details)}))

(defn display-verification-report
  "Display Phase 2 verification results"
  [verification]
  (println \"\\n╔══════════════════════════════════════════════════════════╗\")
  (println \"║          PHASE 2 VERIFICATION REPORT                     ║\")
  (println \"╚══════════════════════════════════════════════════════════╝\\n\")

  (println (if (:seed-match-ok verification)
            \"✅ Optimal seed entropy match ≥ 90%\"
            \"❌ Optimal seed entropy match < 90% (FAIL)\"))

  (println (if (:tagging-complete verification)
            \"✅ Leitmotif tagging ≥ 95% complete\"
            \"❌ Leitmotif tagging < 95% complete (FAIL)\"))

  (println (if (:music-generated verification)
            \"✅ Musical events successfully generated\"
            \"❌ No musical events generated (FAIL)\"))

  (println (if (:quality-acceptable verification)
            \"✅ Tagging quality is good or excellent\"
            \"❌ Tagging quality below acceptable threshold (FAIL)\"))

  (println \"\")
  (println (if (:all-checks-pass verification)
            \"\\n🎉 PHASE 2 PASSED - Ready for Phase 3\"
            \"\\n⚠️  PHASE 2 FAILED - See details above\")))

;; =============================================================================
;; Section 4: Export and Integration Utilities
;; =============================================================================

(defn export-supercollider-code
  "Export SuperCollider code to file for execution"
  [sc-code filepath]
  (spit filepath sc-code)
  {:status :success
   :filepath filepath
   :file-size (count (str sc-code))
   :lines (count (str/split sc-code #\"\\n\"))})

(defn export-phase-2-data
  "Export all Phase 2 results to EDN file for Phase 3"
  [result filepath]
  (let [export-data {:timestamp (System/currentTimeMillis)
                    :phase \"2\"
                    :seed-selection (:seed-selection result)
                    :leitmotif-tagging (:leitmotif-tagging result)
                    :musical-composition (:musical-composition result)
                    :supercollider (:supercollider result)}]

    (spit filepath (pr-str export-data))
    {:status :success
     :filepath filepath
     :data-size (count (str export-data))}))

(defn load-phase-2-checkpoint
  "Load Phase 2 results from checkpoint file"
  [filepath]
  (if (clojure.java.io/file filepath)
    {:status :success
     :data (read-string (slurp filepath))}
    {:status :not-found
     :filepath filepath}))

;; =============================================================================
;; Section 5: Complete Workflow
;; =============================================================================

(defn run-full-phase-2
  "Execute complete Phase 1→2 workflow with all validation"
  [interactions interaction-entropy-baseline
   & {:keys [export-sc-path export-checkpoint-path verbose]
      :or {verbose true}}]

  (when verbose
    (println \"\\n\" (str/upper-case \"=== PHASE 2 COMPLETE WORKFLOW ===\")))

  ;; Execute main pipeline
  (let [result (phase-2-complete-pipeline interactions interaction-entropy-baseline)

        ;; Verify outputs
        verification (verify-phase-2-output result)]

    ;; Display reports
    (when verbose
      (display-phase-2-summary result)
      (display-verification-report verification))

    ;; Export if paths provided
    (when export-sc-path
      (export-supercollider-code (:supercollider-code (:all-data result)) export-sc-path)
      (when verbose
        (println (str \"✅ SuperCollider code exported to: \" export-sc-path))))

    (when export-checkpoint-path
      (export-phase-2-data result export-checkpoint-path)
      (when verbose
        (println (str \"✅ Phase 2 checkpoint exported to: \" export-checkpoint-path))))

    ;; Return result with verification
    (assoc result
           :verification verification
           :status (if (:all-checks-pass verification) :pass :fail))))

;; =============================================================================
;; End of module
;; =============================================================================
