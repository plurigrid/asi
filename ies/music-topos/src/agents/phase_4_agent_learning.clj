(ns agents.phase-4-agent-learning
  "Phase 4: Agent-O-Rama Multi-Agent Training System

  Trains a 9-agent distributed system to recognize and generate patterns:

  Architecture:
  - 9 agents organized in 3×3 grid (Ramanujan expander topology)
  - Each agent: pattern recognizer + generator + novelty detector
  - Agent specialization: Learns archetype patterns from Phase 3
  - Coordination: Entropy monitoring across agent population
  - Learning: Reinforcement via pattern prediction accuracy

  Agent Capabilities:
  1. Pattern Recognition: Classify input patterns into archetypes
  2. Pattern Generation: Generate novel patterns from learned archetypes
  3. Confidence Scoring: Rate prediction certainty
  4. Anomaly Detection: Identify out-of-distribution patterns
  5. Entropy Tracking: Monitor diversity of generated patterns

  Status: 2025-12-21 - Agent training framework ready"
  (:require [clojure.math :as math]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: Agent Data Structure and Initialization
;; =============================================================================

(defn create-agent
  \"Create a single learning agent with internal state\"
  [agent-id archetype-training-data]

  (let [num-training-examples (count archetype-training-data)]
    {:id agent-id
     :created-at (java.util.Date.)
     :training-data archetype-training-data
     :num-examples num-training-examples

     ;; Learning state
     :pattern-memory (vec archetype-training-data)  ; Store all patterns
     :learned-archetypes {}                         ; Archetype models
     :recognition-accuracy 0.0                      ; Prediction accuracy

     ;; Performance metrics
     :predictions-made 0
     :correct-predictions 0
     :false-positives 0
     :false-negatives 0

     ;; Entropy tracking
     :generated-patterns []
     :generation-entropy 0.0

     ;; Anomaly detection
     :detected-anomalies []
     :anomaly-threshold 2.0  ; σ for outlier detection
     :anomaly-count 0}))

(defn initialize-9-agent-topology
  \"Initialize 9 agents in 3×3 grid with training data from Phase 3
   Maps archetypes to agent specialization\"
  [phase-3-training-data]

  (println "\n═══════════════════════════════════════════════════════════════")
  (println "INITIALIZING 9-AGENT TOPOLOGY")
  (println "═══════════════════════════════════════════════════════════════")

  (let [;; Extract archetypes from training data
        archetype-names (keys phase-3-training-data)
        sorted-archetypes (sort archetype-names)

        ;; Create 9 agent IDs in 3×3 grid
        agent-positions (for [row (range 3) col (range 3)]
                          {:agent-id (str "agent-" row "-" col)
                           :position [row col]
                           :grid-index (+ (* row 3) col)})

        ;; Assign archetypes to agents (cyclic distribution)
        agent-assignments (mapv (fn [pos]
                                  (let [archetype-idx (mod (:grid-index pos)
                                                           (count sorted-archetypes))
                                        archetype-name (nth sorted-archetypes archetype-idx)
                                        training-data (get-in phase-3-training-data
                                                            [archetype-name :patterns])
                                        shared-data (dissoc (get phase-3-training-data
                                                                 archetype-name)
                                                           :patterns)]

                                    {:id (:agent-id pos)
                                     :position (:position pos)
                                     :grid-index (:grid-index pos)
                                     :primary-archetype archetype-name
                                     :training-data training-data
                                     :shared-knowledge shared-data}))
                              agent-positions)

        ;; Create agent objects
        agents (mapv (fn [assignment]
                       (create-agent (:id assignment)
                                    (:training-data assignment)))
                    agent-assignments)]

    (println (str "\n✅ Initialized 9 agents in 3×3 topology"))
    (println "\nAgent Assignments:")
    (doseq [assignment agent-assignments]
      (printf "  agent-%d-%d → %s (%d examples)\n"
             (first (:position assignment))
             (second (:position assignment))
             (:primary-archetype assignment)
             (count (:training-data assignment))))
    (println "")

    {:agents agents
     :assignments agent-assignments
     :phase-3-training-data phase-3-training-data
     :topology :ramanujan-3x3}))

;; =============================================================================
;; Section 2: Pattern Recognition and Learning
;; =============================================================================

(defn calculate-pattern-distance
  "Calculate Euclidean distance between two 5D pattern vectors"
  [pattern1 pattern2]
  (let [v1 (:pattern-vector pattern1)
        v2 (:pattern-vector pattern2)]
    (math/sqrt (reduce + (map (fn [a b] (math/pow (- a b) 2)) v1 v2)))))

(defn recognize-pattern
  "Classify a pattern into archetypes using k-NN"
  [agent test-pattern k]

  (let [training-patterns (:pattern-memory agent)
        distances (mapv (fn [train-pattern]
                          (let [dist (calculate-pattern-distance
                                     test-pattern
                                     train-pattern)]
                            {:pattern train-pattern
                             :distance dist}))
                       training-patterns)

        ;; Find k nearest neighbors
        k-nearest (vec (take k (sort-by :distance distances)))
        leitmotifs (map (fn [neighbor]
                          (get-in neighbor [:pattern :leitmotif]))
                       k-nearest)

        ;; Majority voting for classification
        leitmotif-counts (frequencies leitmotifs)
        predicted-leitmotif (key (apply max-key val leitmotif-counts))
        avg-distance (/ (reduce + (map :distance k-nearest)) k)
        confidence (max 0.0 (- 1.0 (* avg-distance 0.3)))  ; Distance-based confidence]

    {:predicted-leitmotif predicted-leitmotif
     :confidence (min 1.0 confidence)
     :k-nearest k-nearest
     :mean-distance avg-distance}))

(defn train-agent-on-examples
  "Train agent by recognizing its own training patterns
   Builds internal model of archetype"
  [agent]

  (let [training-patterns (:pattern-memory agent)
        k (min 3 (max 1 (int (math/floor (/ (count training-patterns) 3)))))

        ;; Run k-NN recognition on all training patterns
        results (mapv (fn [test-pattern]
                       (let [recognition (recognize-pattern agent test-pattern k)
                             actual-leitmotif (:leitmotif test-pattern)
                             predicted (:predicted-leitmotif recognition)
                             correct (= actual-leitmotif predicted)]

                         {:pattern test-pattern
                          :predicted predicted
                          :actual actual-leitmotif
                          :correct correct
                          :confidence (:confidence recognition)}))
                     training-patterns)

        ;; Calculate accuracy
        correct-count (count (filter :correct results))
        total-count (count results)
        accuracy (if (> total-count 0) (/ correct-count total-count) 0.0)
        false-positives (count (filter (fn [r]
                                        (and (:correct r)
                                             (= (:predicted r) (:actual r))))
                                       results))
        false-negatives (count (filter (fn [r]
                                        (and (not (:correct r))
                                             (not= (:predicted r) (:actual r))))
                                       results))]

    ;; Update agent state
    (assoc agent
      :predictions-made total-count
      :correct-predictions correct-count
      :recognition-accuracy accuracy
      :false-positives false-positives
      :false-negatives false-negatives
      :learned-archetypes (frequencies (map :actual training-patterns)))))

;; =============================================================================
;; Section 3: Pattern Generation and Novelty Detection
;; =============================================================================

(defn generate-pattern-variant
  "Generate novel pattern by interpolating between training examples
   Creates new pattern in learned archetype space"
  [agent blend-factor]

  (if (< (count (:pattern-memory agent)) 2)
    nil

    (let [;; Select two random training patterns
          patterns (:pattern-memory agent)
          p1 (rand-nth patterns)
          p2 (rand-nth (filter #(not= % p1) patterns))
          v1 (:pattern-vector p1)
          v2 (:pattern-vector p2)

          ;; Interpolate vectors: p = p1 + blend * (p2 - p1)
          blended-vector (vec (for [i (range 5)]
                               (let [a (nth v1 i)
                                     b (nth v2 i)
                                     component (+ a (* blend-factor (- b a)))]
                                 (min 1.0 (max 0.0 component)))))

          ;; Create new pattern with interpolated vector
          generated-pattern {:pattern-vector blended-vector
                            :leitmotif (if (> blend-factor 0.5)
                                        (:leitmotif p2)
                                        (:leitmotif p1))
                            :generated true
                            :parent-patterns [(:id p1) (:id p2)]
                            :blend-factor blend-factor}]

      generated-pattern)))

(defn generate-patterns-and-track-entropy
  "Generate n novel patterns and track entropy diversity"
  [agent num-patterns]

  (let [;; Generate diverse patterns using different blend factors
        generated (vec (for [i (range num-patterns)]
                        (let [blend (/ (rand) 2.0)]  ; [0, 0.5)
                          (generate-pattern-variant agent blend))))

        ;; Filter out nil patterns
        valid-generated (filter some? generated)

        ;; Calculate entropy of generated patterns
        ;; Entropy based on diversity of leitmotif distribution
        leitmotif-dist (frequencies (map :leitmotif valid-generated))
        total (reduce + (vals leitmotif-dist))
        normalized-dist (mapv (fn [[_ count]]
                               (/ (double count) total))
                             leitmotif-dist)
        entropy (- (reduce + (map (fn [p]
                                  (if (> p 0)
                                    (* p (math/log p))
                                    0.0))
                                leitmotif-dist)))]

    ;; Update agent with generated patterns and entropy
    (assoc agent
      :generated-patterns (into (:generated-patterns agent) valid-generated)
      :generation-entropy entropy)))

(defn detect-anomalies-in-agent-space
  "Identify patterns that are statistical outliers relative to learned patterns"
  [agent test-patterns]

  (let [training-patterns (:pattern-memory agent)
        threshold (:anomaly-threshold agent)

        ;; For each test pattern, calculate mean distance to training set
        anomalies (filter (fn [test-pattern]
                           (let [distances (mapv (fn [train-pattern]
                                                  (calculate-pattern-distance
                                                   test-pattern
                                                   train-pattern))
                                                training-patterns)
                                 mean-dist (/ (reduce + distances)
                                            (count distances))
                                 std-dev (math/sqrt
                                         (/ (reduce + (map (fn [d]
                                                           (math/pow (- d mean-dist) 2))
                                                         distances))
                                            (count distances)))]

                             (> mean-dist (+ mean-dist (* threshold std-dev)))))
                         test-patterns)]

    ;; Update agent anomaly tracking
    (assoc agent
      :detected-anomalies (into (:detected-anomalies agent) anomalies)
      :anomaly-count (+ (:anomaly-count agent) (count anomalies)))))

;; =============================================================================
;; Section 4: Multi-Agent Training Loop
;; =============================================================================

(defn train-agent-population
  "Train all 9 agents on their assigned archetype patterns
   Single training epoch"
  [agent-topology num-generations]

  (println "\n═══════════════════════════════════════════════════════════════")
  (println (str "TRAINING AGENT POPULATION (" num-generations " generations)"))
  (println "═══════════════════════════════════════════════════════════════")

  (let [agents (:agents agent-topology)

        ;; Train each agent on its patterns
        trained-agents (vec (for [generation (range num-generations)]
                             (do
                               (when (zero? (mod generation (max 1 (int (/ num-generations 10)))))
                                 (printf "\n  Generation %d / %d\n" generation num-generations))

                               (mapv (fn [agent]
                                      ;; Step 1: Learn from training data
                                      (let [trained (train-agent-on-examples agent)]

                                        ;; Step 2: Generate novel patterns
                                        (let [with-generation (generate-patterns-and-track-entropy
                                                              trained
                                                              (max 1 (rand-int 5)))]

                                          ;; Step 3: Track anomalies in generated patterns
                                          (if (not-empty (:generated-patterns with-generation))
                                            (detect-anomalies-in-agent-space
                                             with-generation
                                             (:generated-patterns with-generation))
                                            with-generation))))
                                    agents))))

        ;; Flatten and get final state
        final-agents (last trained-agents)]

    (println (str "\n✅ Training complete after " num-generations " generations\n"))

    ;; Print agent statistics
    (doseq [agent final-agents]
      (printf "  %s: accuracy=%.1f%%, entropy=%.2f, anomalies=%d\n"
             (:id agent)
             (* 100 (:recognition-accuracy agent))
             (:generation-entropy agent)
             (:anomaly-count agent)))

    (assoc agent-topology :trained-agents final-agents)))

;; =============================================================================
;; Section 5: Multi-Agent Coordination and Consensus
;; =============================================================================

(defn calculate-population-entropy
  "Calculate diversity (entropy) across all agents' generated patterns"
  [trained-agents]

  (let [all-generated (reduce concat
                             (map :generated-patterns trained-agents))
        leitmotif-dist (frequencies (map :leitmotif all-generated))]

    (if (empty? all-generated)
      0.0
      (- (reduce + (map (fn [[_ count]]
                        (let [p (/ (double count) (count all-generated))]
                          (if (> p 0)
                            (* p (math/log p))
                            0.0)))
                      leitmotif-dist))))))

(defn calculate-population-agreement
  "Measure how much agents agree on pattern classifications"
  [trained-agents test-patterns]

  (if (empty? test-patterns)
    1.0

    (let [k 1  ; Use nearest neighbor for speed

          ;; Get predictions from all agents
          predictions (mapv (fn [agent]
                            (mapv (fn [pattern]
                                  (:predicted-leitmotif
                                   (recognize-pattern agent pattern k)))
                                test-patterns))
                          trained-agents)

          ;; Calculate agreement (percentage where all agents agree)
          agreed (count (filter (fn [predictions-for-pattern]
                                (= 1 (count (frequencies predictions-for-pattern))))
                              (apply mapv vector predictions)))

          total (count test-patterns)]

      (if (> total 0)
        (/ (double agreed) total)
        1.0))))

;; =============================================================================
;; Section 6: Phase 4 Integration
;; =============================================================================

(defn run-phase-4
  "Execute complete Phase 3→4 agent training pipeline
   Input: Phase 3 training data
   Output: Trained agent population ready for Phase 5"
  [phase-3-training-data num-training-generations]

  (println "\n╔═══════════════════════════════════════════════════════════╗")
  (println "║    PHASE 4: AGENT-O-RAMA MULTI-AGENT TRAINING           ║")
  (println "║         (Phase 3→4 Integration Pipeline)                 ║")
  (println "╚═══════════════════════════════════════════════════════════╝")

  ;; Step 1: Initialize 9-agent topology
  (let [topology (initialize-9-agent-topology phase-3-training-data)

        ;; Step 2: Train agents on archetype patterns
        trained-topology (train-agent-population topology num-training-generations)
        trained-agents (:trained-agents trained-topology)

        ;; Step 3: Calculate population metrics
        pop-entropy (calculate-population-entropy trained-agents)
        test-patterns (take 10 (reduce concat
                               (map #(get-in % [:training-data])
                                   phase-3-training-data)))
        pop-agreement (calculate-population-agreement trained-agents test-patterns)]

    ;; Summary
    (println "\n╔═══════════════════════════════════════════════════════════╗")
    (println "║       PHASE 4 TRAINING COMPLETE - SUMMARY               ║")
    (println "╚═══════════════════════════════════════════════════════════╝\n")

    (println "📊 POPULATION METRICS")
    (println "─────────────────────────────────────────────────────────")
    (printf "  Population Entropy: %.3f\n" pop-entropy)
    (printf "  Agent Agreement: %.1f%%\n" (* 100 pop-agreement))
    (println "")

    (println "🤖 INDIVIDUAL AGENT STATS")
    (println "─────────────────────────────────────────────────────────")
    (let [avg-accuracy (/ (reduce + (map :recognition-accuracy trained-agents))
                         (count trained-agents))
          avg-entropy (/ (reduce + (map :generation-entropy trained-agents))
                        (count trained-agents))
          total-anomalies (reduce + (map :anomaly-count trained-agents))]

      (printf "  Average Accuracy: %.1f%%\n" (* 100 avg-accuracy))
      (printf "  Average Entropy: %.3f\n" avg-entropy)
      (printf "  Total Anomalies Detected: %d\n" total-anomalies))
    (println "")

    {:phase "4"
     :status :complete
     :agent-topology topology
     :trained-agents trained-agents
     :population-metrics {:entropy pop-entropy
                         :agreement pop-agreement
                         :num-agents (count trained-agents)
                         :num-generations num-training-generations}
     :phase-3-training-data phase-3-training-data}))
