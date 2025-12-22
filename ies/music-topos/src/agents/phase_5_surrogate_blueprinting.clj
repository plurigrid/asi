(ns agents.phase-5-surrogate-blueprinting
  "Phase 5: Surrogate Blueprinting

   Transforms Phase 4 trained agents into reusable surrogate blueprints.
   Each blueprint encapsulates:
   - Learned archetype distributions (probability, mean, covariance)
   - Recognition accuracy and generation entropy metrics
   - Girard polarity assignment (RED/BLUE/GREEN)
   - Expertise specialization map

   Enables: Composable surrogate agents with verifiable properties
   Status: 2025-12-21 - Blueprint extraction framework"
  (:require [clojure.math :as math]
            [clojure.data.json :as json]))

;; =============================================================================
;; Section 1: Archetype Distribution Models
;; =============================================================================

(defn compute-archetype-distribution
  "Extract probability distribution for recognized patterns
   Input: list of recognized leitmotifs
   Output: {leitmotif -> frequency_count}"
  [recognized-patterns]

  (let [leitmotif-freqs (frequencies recognized-patterns)]
    (into {}
          (for [[leitmotif count] leitmotif-freqs]
            [leitmotif {:count count
                       :probability (/ count (count recognized-patterns))}]))))

(defn compute-vector-statistics
  "Calculate mean and covariance for pattern vectors
   Input: list of 5D pattern vectors for a specific archetype
   Output: {:mean [...], :covariance [[...] ...]}"
  [pattern-vectors]

  (if (empty? pattern-vectors)
    {:mean [0 0 0 0 0]
     :covariance (vec (repeat 5 (vec (repeat 5 0))))}

    (let [n (count pattern-vectors)
          ;; Compute mean
          mean (vec (for [dim (range 5)]
                     (/ (reduce + (map #(nth % dim) pattern-vectors))
                        n)))

          ;; Compute covariance matrix
          centered (map (fn [v]
                         (vec (for [dim (range 5)]
                                (- (nth v dim) (nth mean dim)))))
                       pattern-vectors)

          covariance (vec (for [i (range 5)]
                           (vec (for [j (range 5)]
                                  (/ (reduce + (map (fn [v]
                                                      (* (nth v i)
                                                         (nth v j)))
                                                    centered))
                                     (max 1 (dec n)))))))]

      {:mean mean
       :covariance covariance})))

(defn build-archetype-model
  "Create a complete distribution model for one archetype
   Input: archetype-name, list of patterns recognized as this archetype
   Output: {:probability, :mean-vector, :covariance-matrix, :sample-count}"
  [archetype-name patterns-of-archetype all-patterns]

  (let [sample-count (count patterns-of-archetype)
        probability (/ sample-count (count all-patterns))
        pattern-vectors (map :pattern-vector patterns-of-archetype)
        {:keys [mean covariance]} (compute-vector-statistics pattern-vectors)]

    {:archetype-name archetype-name
     :probability probability
     :sample-count sample-count
     :mean-vector mean
     :covariance-matrix covariance
     :dimension-names [:topic :mode :temporal :network :length]}))

;; =============================================================================
;; Section 2: Surrogate Blueprint Extraction
;; =============================================================================

(defn extract-learned-archetypes-from-agent
  "Pull out all archetype distributions that the agent learned
   Input: trained agent from Phase 4
   Output: map of archetype -> distribution info"
  [agent]

  (let [pattern-memory (:pattern-memory agent)
        learned-archetypes (:learned-archetypes agent)]

    (into {}
          (for [[archetype count] learned-archetypes]
            ;; Find all patterns of this archetype
            (let [patterns-of-archetype (filter #(= (:leitmotif %) archetype)
                                                pattern-memory)
                  model (build-archetype-model archetype
                                              patterns-of-archetype
                                              pattern-memory)]
              [archetype model])))))

(defn assign-girard-polarity-heuristic
  "Determine Girard color based on agent characteristics
   - RED (positive): high entropy → good generator
   - BLUE (negative): high accuracy → good recognizer
   - GREEN (neutral): balanced → integrator"
  [agent-metrics]

  (let [{:keys [recognition-accuracy generation-entropy]} agent-metrics
        entropy-threshold 1.8
        accuracy-threshold 0.75]

    (cond
      (> generation-entropy entropy-threshold) :red    ; good generator
      (> recognition-accuracy accuracy-threshold) :blue ; good recognizer
      :else :green)))                                   ; balanced

(defn surrogate-blueprint-from-agent
  "Main function: extract complete blueprint from trained agent

   Input: trained-agent (from Phase 4)
   Output: immutable blueprint specification ready for deployment"
  [agent]

  (let [agent-id (:id agent)
        pattern-memory (:pattern-memory agent)
        learned-archetypes (extract-learned-archetypes-from-agent agent)
        recognition-accuracy (:recognition-accuracy agent)
        generation-entropy (:generation-entropy agent)
        anomaly-count (:anomaly-count agent)

        ;; Compute anomaly detection threshold (2 sigma)
        anomaly-threshold (if (> anomaly-count 0)
                           (/ anomaly-count (count pattern-memory))
                           0.05)

        ;; Assign Girard polarity
        girard-polarity (assign-girard-polarity-heuristic
                         {:recognition-accuracy recognition-accuracy
                          :generation-entropy generation-entropy})

        ;; Determine role based on metrics
        role (case girard-polarity
               :red :generator
               :blue :recognizer
               :green :integrator)]

    {:blueprint-version "1.0"
     :created-at (java.util.Date.)
     :agent-id agent-id

     ;; Core specialization
     :archetype-models learned-archetypes
     :primary-archetype (first (keys (sort-by (fn [[k v]]
                                                (- (:probability v)))
                                              learned-archetypes)))

     ;; Metrics from training
     :recognition-accuracy recognition-accuracy
     :generation-entropy generation-entropy
     :anomaly-count anomaly-count
     :anomaly-detection-threshold anomaly-threshold
     :total-patterns-trained (count pattern-memory)

     ;; Role and polarity
     :girard-polarity girard-polarity
     :role role
     :color-characteristics (case girard-polarity
                              :red {:hue 0 :chroma 100 :lightness 50}      ; RED
                              :blue {:hue 240 :chroma 100 :lightness 45}   ; BLUE
                              :green {:hue 120 :chroma 80 :lightness 50})})) ; GREEN

(defn extract-expertise-map
  "Create specialization index: archetype -> expertise_score

   Expertise score = f(accuracy on that archetype, entropy, anomaly rate)
   Range: [0, 1] where 1 = perfect expertise"
  [agent]

  (let [archetype-models (extract-learned-archetypes-from-agent agent)
        base-accuracy (:recognition-accuracy agent)
        generation-entropy (:generation-entropy agent)

        ;; Normalize entropy to [0, 1]
        normalized-entropy (min 1.0 (/ generation-entropy 5.0))]

    (into {}
          (for [[archetype model] archetype-models]
            (let [;; Expertise = (accuracy on this archetype) + (probability of this archetype)
                  ;; Higher probability + good accuracy = higher expertise
                  probability (:probability model)
                  expertise (min 1.0
                            (* base-accuracy
                               probability
                               (+ 0.5 (* 0.5 normalized-entropy))))]

              [archetype expertise])))))

;; =============================================================================
;; Section 3: Blueprint Composition and Validation
;; =============================================================================

(defn validate-blueprint-structure
  "Sanity check: ensure blueprint has all required fields
   Input: blueprint
   Output: true if valid, throws exception if not"
  [blueprint]

  (let [required-fields [:blueprint-version :agent-id :archetype-models
                        :recognition-accuracy :generation-entropy
                        :girard-polarity :role]]

    (doseq [field required-fields]
      (when-not (contains? blueprint field)
        (throw (ex-info (str "Missing required field: " field)
                       {:blueprint blueprint :field field}))))

    ;; Validate ranges
    (assert (>= (:recognition-accuracy blueprint) 0.0)
            "Accuracy must be non-negative")
    (assert (<= (:recognition-accuracy blueprint) 1.0)
            "Accuracy must be <= 1.0")
    (assert (>= (:generation-entropy blueprint) 0.0)
            "Entropy must be non-negative")
    (assert (#{:red :blue :green} (:girard-polarity blueprint))
            "Polarity must be RED, BLUE, or GREEN")

    true))

(defn blueprint-similarity-score
  "Measure how similar two blueprints are (for clustering)
   Input: blueprint1, blueprint2
   Output: similarity ∈ [0, 1]"
  [blueprint1 blueprint2]

  (let [;; Same primary archetype?
        same-primary (if (= (:primary-archetype blueprint1)
                           (:primary-archetype blueprint2))
                       0.3 0.0)

        ;; Similar accuracy?
        acc-diff (Math/abs (- (:recognition-accuracy blueprint1)
                             (:recognition-accuracy blueprint2)))
        accuracy-sim (max 0.0 (- 1.0 acc-diff))

        ;; Similar entropy?
        entropy-diff (Math/abs (- (:generation-entropy blueprint1)
                                 (:generation-entropy blueprint2)))
        entropy-sim (max 0.0 (- 1.0 (/ entropy-diff 5.0)))

        ;; Same polarity?
        same-polarity (if (= (:girard-polarity blueprint1)
                            (:girard-polarity blueprint2))
                        0.2 0.0)]

    (min 1.0 (+ same-primary
               (* 0.2 accuracy-sim)
               (* 0.2 entropy-sim)
               same-polarity))))

;; =============================================================================
;; Section 4: Network-wide Blueprint Management
;; =============================================================================

(defn create-agent-expertise-map
  "Create a 9-agent expertise registry
   Input: list of 9 agent blueprints
   Output: agent-id -> expertise-map"
  [agent-blueprints]

  (into {}
        (for [blueprint agent-blueprints]
          [(:agent-id blueprint)
           (extract-expertise-map
            ;; Reconstruct agent object from blueprint for extraction
            {:id (:agent-id blueprint)
             :pattern-memory []  ; not needed for this calculation
             :recognition-accuracy (:recognition-accuracy blueprint)
             :generation-entropy (:generation-entropy blueprint)
             :learned-archetypes (into {}
                                       (for [[arch model] (:archetype-models blueprint)]
                                         [arch (:sample-count model)]))})])))

(defn build-network-configuration
  "Generate NATS/deployment configuration for 9-agent network
   Input: 9 agent blueprints + population metrics
   Output: network config with agent assignments and roles"
  [agent-blueprints population-metrics]

  (validate-blueprint-structure (first agent-blueprints))

  (let [;; Assign 3×3 grid positions
        positions (for [row (range 3) col (range 3)]
                   [row col])

        ;; Sort blueprints by polarity for balanced distribution
        red-agents (filter #(= :red (:girard-polarity %)) agent-blueprints)
        blue-agents (filter #(= :blue (:girard-polarity %)) agent-blueprints)
        green-agents (filter #(= :green (:girard-polarity %)) agent-blueprints)

        ;; Create deployment specs
        agent-specs (vec (for [[blueprint position] (map vector
                                                          agent-blueprints
                                                          positions)]
                          {:agent-id (:agent-id blueprint)
                           :position position
                           :girard-polarity (:girard-polarity blueprint)
                           :role (:role blueprint)
                           :primary-archetype (:primary-archetype blueprint)
                           :accuracy (:recognition-accuracy blueprint)
                           :entropy (:generation-entropy blueprint)
                           :nats-subject (str "agents.agent-"
                                            (nth position 0) "-"
                                            (nth position 1))}))]

    {:network-version "1.0"
     :created-at (java.util.Date.)
     :topology :ramanujan-3x3
     :num-agents 9
     :population-metrics population-metrics
     :agent-assignments agent-specs
     :polarity-distribution {:red (count red-agents)
                            :blue (count blue-agents)
                            :green (count green-agents)}
     :nats-broker-url "nats://localhost:4222"
     :nats-subjects {:heartbeat "agents.heartbeat.{agent-id}"
                    :pattern "agents.pattern.{agent-id}"
                    :request "agents.request.{agent-id}"
                    :response "agents.response.{agent-id}"
                    :population-entropy "population.entropy"
                    :network-topology "network.topology"}}))

;; =============================================================================
;; Section 5: Blueprint Serialization and Export
;; =============================================================================

(defn blueprint-to-edn-string
  "Serialize blueprint to EDN for storage/transmission
   Input: blueprint
   Output: EDN string"
  [blueprint]

  (validate-blueprint-structure blueprint)

  (pr-str (dissoc blueprint :created-at :color-characteristics)))

(defn edn-string-to-blueprint
  "Deserialize EDN blueprint
   Input: EDN string
   Output: blueprint"
  [edn-string]

  (let [blueprint (read-string edn-string)]
    (validate-blueprint-structure blueprint)
    (assoc blueprint :created-at (java.util.Date.))))

(defn export-all-blueprints
  "Export all 9 agent blueprints to file
   Input: list of blueprints, file path
   Output: true on success"
  [blueprints export-path]

  (println (str "📦 Exporting " (count blueprints) " blueprints to " export-path))

  (try
    (let [export-data {:blueprints (vec blueprints)
                      :count (count blueprints)
                      :exported-at (java.util.Date.)}
          edn-content (pr-str export-data)]

      (spit export-path edn-content)

      (println (str "✅ Exported " (count blueprints) " blueprints "
                   "(" (count edn-content) " bytes)"))
      true)

    (catch Exception e
      (println (str "❌ Export failed: " (.getMessage e)))
      false)))

(defn import-blueprints
  "Import previously exported blueprints from file
   Input: file path
   Output: list of blueprints"
  [import-path]

  (println (str "📦 Importing blueprints from " import-path))

  (try
    (let [edn-content (slurp import-path)
          data (read-string edn-content)
          blueprints (:blueprints data)]

      (doseq [blueprint blueprints]
        (validate-blueprint-structure blueprint))

      (println (str "✅ Imported " (count blueprints) " blueprints"))
      blueprints)

    (catch Exception e
      (println (str "❌ Import failed: " (.getMessage e)))
      [])))

;; =============================================================================
;; Section 6: Phase 4→5 Transition Integration
;; =============================================================================

(defn process-phase4-result
  "Main entry point: transform Phase 4 output into Phase 5 blueprints

   Input: phase-4-result (contains :trained-agents and :population-metrics)
   Output: {:blueprints [...], :network-config {...}, :expertise-maps {...}}"
  [phase-4-result]

  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║   PHASE 5: SURROGATE BLUEPRINTING                      ║")
  (println "║       (Phase 4→5 Blueprint Extraction)                 ║")
  (println "╚══════════════════════════════════════════════════════════╝\n")

  (let [trained-agents (:trained-agents phase-4-result)
        population-metrics (:population-metrics phase-4-result)

        ;; Extract blueprints from all 9 agents
        blueprints (vec (for [agent trained-agents]
                         (surrogate-blueprint-from-agent agent)))

        ;; Validate all blueprints
        _ (doseq [blueprint blueprints]
            (validate-blueprint-structure blueprint))

        ;; Build expertise maps
        expertise-maps (create-agent-expertise-map blueprints)

        ;; Create network configuration
        network-config (build-network-configuration blueprints population-metrics)]

    (println "📊 BLUEPRINT EXTRACTION COMPLETE")
    (println "─────────────────────────────────────────────────────────")
    (println (str "  Blueprints created: " (count blueprints)))
    (println (str "  Population entropy: " (format "%.3f" (:entropy population-metrics))))
    (println (str "  Population agreement: " (format "%.1f%%"
                                                    (* 100 (:agreement population-metrics)))))
    (println "")

    (println "🎨 GIRARD POLARITY DISTRIBUTION")
    (println "─────────────────────────────────────────────────────────")
    (doseq [blueprint blueprints]
      (printf "  %s: %s (role: %s, accuracy: %.1f%%)%n"
             (:agent-id blueprint)
             (name (:girard-polarity blueprint))
             (name (:role blueprint))
             (* 100 (:recognition-accuracy blueprint))))
    (println "")

    (println "🧠 EXPERTISE SPECIALIZATION")
    (println "─────────────────────────────────────────────────────────")
    (doseq [[agent-id expertise] expertise-maps]
      (let [top-archetypes (take 3 (sort-by (fn [[k v]] (- v)) expertise))]
        (printf "  %s specializes in: %s%n"
               agent-id
               (str/join ", " (for [[arch score] top-archetypes]
                               (str (name arch) "(" (format "%.2f" score) ")"))))))
    (println "")

    {:phase "5-blueprinting"
     :status :complete
     :blueprints blueprints
     :network-config network-config
     :expertise-maps expertise-maps
     :population-metrics population-metrics
     :phase-4-result phase-4-result}))

;; =============================================================================
;; Section 7: Quality Assurance
;; =============================================================================

(defn blueprint-quality-report
  "Generate comprehensive QA report on all blueprints
   Input: blueprint list
   Output: report with statistics and alerts"
  [blueprints]

  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║         BLUEPRINT QUALITY ASSURANCE REPORT             ║")
  (println "╚══════════════════════════════════════════════════════════╝\n")

  (let [num-blueprints (count blueprints)
        avg-accuracy (/ (reduce + (map :recognition-accuracy blueprints))
                       num-blueprints)
        avg-entropy (/ (reduce + (map :generation-entropy blueprints))
                      num-blueprints)

        red-count (count (filter #(= :red (:girard-polarity %)) blueprints))
        blue-count (count (filter #(= :blue (:girard-polarity %)) blueprints))
        green-count (count (filter #(= :green (:girard-polarity %)) blueprints))

        valid-blueprints (count (filter (fn [bp]
                                         (try
                                           (validate-blueprint-structure bp)
                                           true
                                           (catch Exception _ false)))
                                       blueprints))]

    (println "📈 METRICS SUMMARY")
    (println "─────────────────────────────────────────────────────────")
    (printf "  Total blueprints: %d%n" num-blueprints)
    (printf "  Valid blueprints: %d%n" valid-blueprints)
    (printf "  Average accuracy: %.1f%%%n" (* 100 avg-accuracy))
    (printf "  Average entropy: %.3f%n" avg-entropy)
    (println "")

    (println "🎨 POLARITY DISTRIBUTION")
    (println "─────────────────────────────────────────────────────────")
    (printf "  RED (generators): %d%n" red-count)
    (printf "  BLUE (recognizers): %d%n" blue-count)
    (printf "  GREEN (integrators): %d%n" green-count)
    (println "")

    (println "✅ STATUS")
    (println "─────────────────────────────────────────────────────────")
    (if (= valid-blueprints num-blueprints)
      (println "  All blueprints valid!")
      (println (str "  WARNING: " (- num-blueprints valid-blueprints)
                   " invalid blueprints")))

    (if (> avg-accuracy 0.7)
      (println "  Accuracy targets met (> 70%)")
      (println "  WARNING: Accuracy below target"))

    {:num-blueprints num-blueprints
     :valid-blueprints valid-blueprints
     :avg-accuracy avg-accuracy
     :avg-entropy avg-entropy
     :polarity-distribution {:red red-count :blue blue-count :green green-count}}))

(require '[clojure.string :as str])
