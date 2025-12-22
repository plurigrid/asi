(ns agents.phase-3-pattern-extraction
  "Phase 3: Extract and Analyze 5D Patterns from Phase 2 Leitmotif Tags

  Builds on Phase 2 output:
  - Takes tagged interactions with leitmotif assignments
  - Extracts 5D patterns: topic, mode, temporal, network, length
  - Performs clustering and dimensionality reduction
  - Identifies pattern archetypes and anomalies
  - Prepares pattern descriptors for Phase 4 agent training

  Output: Pattern clusters, archetypes, anomalies for multi-agent learning

  Status: 2025-12-21 - Phase 2→3 transition ready"
  (:require [clojure.math :as math]
            [clojure.set :as set]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: 5D Pattern Extraction from Leitmotif Tags
;; =============================================================================

(defn extract-5d-pattern
  "Extract 5D pattern vector from a tagged interaction
   Dimensions: [topic, mode, temporal, network, length]"
  [interaction leitmotif-tag entropy-baseline]

  (let [;; Topic dimension: 0-1 based on leitmotif category
        topic-score (case leitmotif-tag
                      :technical-innovation 0.95
                      :collaborative-work 0.75
                      :philosophical-reflection 0.60
                      :network-building 0.80
                      :musical-creation 0.85
                      :synthesis 0.70
                      0.5)  ; Unknown default

        ;; Mode dimension: 0-1 based on interaction type
        mode-score (let [is-reply (some? (:in-reply-to interaction))
                        mentions (or (:mentions-count interaction) 0)
                        collab (or (:collaborators-count interaction) 0)]
                    (cond (and is-reply (> collab 0)) 0.95  ; Reply + collaboration
                          is-reply 0.70                    ; Just reply
                          (> collab 0) 0.85                ; Just collaboration
                          (> mentions 0) 0.60              ; Just mentions
                          :else 0.40))                     ; Standalone

        ;; Temporal dimension: Entropy of posting time patterns
        ;; Higher entropy = more irregular posting patterns
        temporal-entropy (if (pos? entropy-baseline)
                          (min 1.0 (/ (:temporal entropy-baseline 2.0) 3.0))
                          0.5)

        ;; Network dimension: Connection diversity
        ;; Based on mentions + collaborators + links
        network-score (let [mentions (or (:mentions-count interaction) 0)
                           collab (or (:collaborators-count interaction) 0)
                           links (or (:links-count interaction) 0)
                           total-connections (+ mentions collab (* 2 links))]
                       (min 1.0 (/ total-connections 5.0)))

        ;; Length dimension: Expression verbosity
        ;; Normalized by content length
        content-length (count (:content interaction ""))
        length-score (min 1.0 (/ content-length 500.0))]

    {:leitmotif leitmotif-tag
     :pattern-vector [topic-score mode-score temporal-entropy network-score length-score]
     :dimensions {:topic topic-score
                 :mode mode-score
                 :temporal temporal-entropy
                 :network network-score
                 :length length-score}
     :interaction-id (:id interaction)
     :timestamp (:timestamp interaction)}))

(defn extract-all-5d-patterns
  "Extract 5D pattern vectors from all tagged interactions"
  [tagged-interactions entropy-baseline]

  (mapv (fn [interaction]
          (let [leitmotif-tag (or (:primary-leitmotif interaction) :synthesis)]
            (extract-5d-pattern interaction leitmotif-tag entropy-baseline)))
        tagged-interactions))

;; =============================================================================
;; Section 2: Pattern Clustering via K-Means
;; =============================================================================

(defn euclidean-distance
  "Calculate Euclidean distance between two 5D vectors"
  [v1 v2]
  (math/sqrt (reduce + (map (fn [a b] (math/pow (- a b) 2)) v1 v2))))

(defn initialize-clusters
  "Initialize k random cluster centers from pattern vectors"
  [patterns k]
  (let [shuffled (shuffle patterns)]
    (vec (take k (map :pattern-vector shuffled)))))

(defn assign-patterns-to-clusters
  "Assign each pattern to nearest cluster center"
  [patterns cluster-centers]
  (mapv (fn [pattern]
          (let [distances (mapv (fn [center]
                                  (euclidean-distance (:pattern-vector pattern) center))
                                cluster-centers)
                nearest-idx (apply min-key distances (range (count distances)))]
            (assoc pattern :cluster nearest-idx)))
        patterns))

(defn update-cluster-centers
  "Update cluster centers as mean of assigned patterns"
  [patterns cluster-centers num-clusters]
  (vec (for [k (range num-clusters)]
         (let [cluster-patterns (filter #(= (:cluster %) k) patterns)
               vectors (map :pattern-vector cluster-patterns)]
           (if (empty? vectors)
             (nth cluster-centers k)  ; Keep old center if empty
             (vec (for [dim (range 5)]
                    (/ (reduce + (map #(nth % dim) vectors))
                       (count vectors)))))))))

(defn kmeans-cluster
  "Perform K-means clustering on 5D pattern vectors
   Returns map of cluster ID to patterns"
  [patterns k max-iterations]
  (println (str "\n📊 K-Means Clustering (k=" k ", max iterations=" max-iterations ")"))
  (println "─────────────────────────────────────────────────────────")

  (loop [cluster-centers (initialize-clusters patterns k)
         iteration 0
         old-centers nil]

    (let [assigned (assign-patterns-to-clusters patterns cluster-centers)
          new-centers (update-cluster-centers assigned cluster-centers k)]

      (if (or (>= iteration max-iterations)
              (= old-centers new-centers))
        (do
          (println (str "✅ Converged after " iteration " iterations"))
          (let [by-cluster (group-by :cluster assigned)]
            (doseq [[cluster-id cluster-patterns] (sort-by key by-cluster)]
              (printf "  Cluster %d: %d patterns\n" cluster-id (count cluster-patterns)))
            by-cluster))

        (do
          (when (zero? (mod iteration 10))
            (println (str "   Iteration " iteration "...")))
          (recur new-centers
                 (inc iteration)
                 cluster-centers))))))

;; =============================================================================
;; Section 3: Pattern Archetype Identification
;; =============================================================================

(defn calculate-cluster-centroid
  "Calculate mean position of cluster in 5D space"
  [cluster-patterns]
  (let [vectors (map :pattern-vector cluster-patterns)
        num-patterns (count vectors)]
    (vec (for [dim (range 5)]
           (/ (reduce + (map #(nth % dim) vectors))
              num-patterns)))))

(defn cluster-stats
  "Calculate statistics for a cluster"
  [cluster-patterns centroid]
  (let [vectors (map :pattern-vector cluster-patterns)
        distances (map (fn [v] (euclidean-distance v centroid)) vectors)
        leitmotif-counts (frequencies (map :leitmotif cluster-patterns))]

    {:size (count cluster-patterns)
     :centroid centroid
     :mean-radius (/ (reduce + distances) (count distances))
     :dominant-leitmotif (key (apply max-key val leitmotif-counts))
     :leitmotif-distribution leitmotif-counts
     :dimension-means {:topic (nth centroid 0)
                      :mode (nth centroid 1)
                      :temporal (nth centroid 2)
                      :network (nth centroid 3)
                      :length (nth centroid 4)}}))

(defn identify-archetypes
  "Identify pattern archetypes from clusters"
  [cluster-map]
  (println "\n🎭 Archetype Identification")
  (println "─────────────────────────────────────────────────────────")

  (let [archetypes (reduce (fn [acc [cluster-id patterns]]
                            (let [centroid (calculate-cluster-centroid patterns)
                                  stats (cluster-stats patterns centroid)
                                  archetype-name (str "Archetype-" (inc (count acc)))
                                  dominant-leitmotif (:dominant-leitmotif stats)]

                              (assoc acc
                                archetype-name
                                (assoc stats
                                  :cluster-id cluster-id
                                  :name archetype-name
                                  :dominant-leitmotif dominant-leitmotif))))
                           {}
                           cluster-map)]

    (doseq [[name archetype] (sort-by key archetypes)]
      (printf "  %s (cluster %d): %d patterns\n"
             name
             (:cluster-id archetype)
             (:size archetype))
      (printf "    Dominant: %s\n" (:dominant-leitmotif archetype))
      (printf "    Characteristics: topic=%.2f, mode=%.2f, temporal=%.2f, network=%.2f, length=%.2f\n"
             (-> archetype :dimension-means :topic)
             (-> archetype :dimension-means :mode)
             (-> archetype :dimension-means :temporal)
             (-> archetype :dimension-means :network)
             (-> archetype :dimension-means :length)))

    archetypes))

;; =============================================================================
;; Section 4: Anomaly Detection
;; =============================================================================

(defn detect-anomalies
  "Identify patterns that are statistical outliers
   Anomalies have distance > 2σ from cluster mean"
  [cluster-patterns centroid]
  (let [vectors (map :pattern-vector cluster-patterns)
        distances (mapv (fn [v] (euclidean-distance v centroid)) vectors)
        mean-distance (/ (reduce + distances) (count distances))
        variance (/ (reduce + (map (fn [d]
                                    (math/pow (- d mean-distance) 2))
                                  distances))
                   (count distances))
        std-dev (math/sqrt variance)
        threshold (+ mean-distance (* 2 std-dev))]

    (filter (fn [pattern]
              (let [distance (euclidean-distance (:pattern-vector pattern) centroid)]
                (> distance threshold)))
            cluster-patterns)))

(defn identify-all-anomalies
  "Find anomalous patterns across all clusters"
  [cluster-map]
  (println "\n⚠️  Anomaly Detection")
  (println "─────────────────────────────────────────────────────────")

  (let [anomalies (reduce (fn [acc [cluster-id patterns]]
                           (let [centroid (calculate-cluster-centroid patterns)
                                 cluster-anomalies (detect-anomalies patterns centroid)]
                             (concat acc
                                    (map (fn [pattern]
                                           (assoc pattern :anomaly-cluster cluster-id))
                                        cluster-anomalies))))
                         []
                         cluster-map)]

    (println (str "✅ Found " (count anomalies) " anomalous patterns"))
    (if (> (count anomalies) 0)
      (do
        (printf "   Top anomalies by cluster:\n")
        (doseq [[cluster-id cluster-anomalies]
                (sort-by key (group-by :anomaly-cluster anomalies))]
          (printf "     Cluster %d: %d anomalies\n" cluster-id (count cluster-anomalies)))))

    anomalies))

;; =============================================================================
;; Section 5: Dimensionality Reduction (PCA-like)
;; =============================================================================

(defn calculate-pattern-variance
  "Calculate variance along each dimension"
  [patterns]
  (let [vectors (map :pattern-vector patterns)
        num-patterns (count vectors)
        means (vec (for [dim (range 5)]
                    (/ (reduce + (map #(nth % dim) vectors))
                       num-patterns)))]

    (vec (for [dim (range 5)]
           (let [dim-variance (reduce + (map (fn [v]
                                              (math/pow (- (nth v dim)
                                                          (nth means dim))
                                                       2))
                                            vectors))]
             (/ dim-variance num-patterns))))))

(defn dimension-importance
  "Rank dimensions by variance importance"
  [patterns]
  (println "\n📐 Dimensionality Analysis")
  (println "─────────────────────────────────────────────────────────")

  (let [variances (calculate-pattern-variance patterns)
        total-variance (reduce + variances)
        importance (mapv (fn [v] (/ v total-variance)) variances)
        dims [:topic :mode :temporal :network :length]]

    (doseq [[dim-name variance imp] (map vector dims variances importance)]
      (printf "  %s: %.3f variance (%.1f%% importance)\n"
             (str/upper-case (str dim-name))
             variance
             (* 100 imp)))

    {:variances variances
     :importance importance
     :dimensions dims}))

;; =============================================================================
;; Section 6: Phase 3 Integration
;; =============================================================================

(defn run-phase-3
  "Complete Phase 2→3 pattern extraction pipeline
   Input: Phase 2 result map
   Output: Pattern clusters, archetypes, anomalies"
  [phase-2-result]

  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║     PHASE 3: 5D PATTERN EXTRACTION & CLUSTERING        ║")
  (println "╚══════════════════════════════════════════════════════════╝")

  (let [tagged-interactions (get-in phase-2-result [:all-data :tagged-interactions])
        entropy-baseline (get-in phase-2-result [:seed-selection])

        ;; Step 1: Extract 5D patterns
        _step1 (println "\n✨ STEP 1: Extract 5D Patterns from Leitmotifs")
        patterns (extract-all-5d-patterns tagged-interactions entropy-baseline)
        _ (println (str "  Extracted " (count patterns) " 5D pattern vectors"))
        _ (println "")

        ;; Step 2: Perform K-means clustering
        ;; Heuristic: k = sqrt(n) / 2
        num-clusters (max 3 (int (math/floor (/ (math/sqrt (count patterns)) 2))))
        _step2 (println "\n🔀 STEP 2: K-Means Clustering")
        cluster-map (kmeans-cluster patterns num-clusters 100)
        _ (println "")

        ;; Step 3: Identify archetypes
        _step3 (println "\n🎭 STEP 3: Identify Pattern Archetypes")
        archetypes (identify-archetypes cluster-map)
        _ (println "")

        ;; Step 4: Detect anomalies
        _step4 (println "\n⚠️  STEP 4: Detect Anomalies")
        anomalies (identify-all-anomalies cluster-map)
        _ (println "")

        ;; Step 5: Analyze dimensionality
        _step5 (println "\n📊 STEP 5: Dimensionality Analysis")
        dimension-analysis (dimension-importance patterns)
        _ (println "")]

    ;; Summary
    (println "\n╔══════════════════════════════════════════════════════════╗")
    (println "║       PHASE 3 EXTRACTION COMPLETE - SUMMARY             ║")
    (println "╚══════════════════════════════════════════════════════════╝")

    {:phase "3"
     :status :complete
     :pattern-extraction {:total-patterns (count patterns)
                         :sample-patterns (take 3 patterns)}

     :clustering {:num-clusters num-clusters
                 :clusters-map cluster-map
                 :cluster-sizes (mapv (fn [[id ps]] [id (count ps)])
                                     cluster-map)}

     :archetypes archetypes

     :anomalies {:total-anomalies (count anomalies)
                :anomalies-by-cluster (frequencies (map :anomaly-cluster anomalies))
                :sample-anomalies (take 3 anomalies)}

     :dimensionality dimension-analysis

     :all-data {:patterns patterns
               :full-cluster-map cluster-map
               :all-anomalies anomalies
               :phase-2-result phase-2-result}}))

;; =============================================================================
;; Section 7: Export Functions
;; =============================================================================

(defn export-patterns-to-edn
  "Export pattern analysis to EDN checkpoint"
  [phase-3-result filepath]
  (println (str "\n💾 Exporting Phase 3 results to " filepath))
  (spit filepath (pr-str phase-3-result))
  (println "✅ Export complete"))

(defn export-pattern-summary
  "Export human-readable pattern summary"
  [phase-3-result filepath]
  (let [summary-lines
        [(str "Phase 3: 5D Pattern Extraction - " (java.util.Date.))
         ""
         (str "Total Patterns: " (get-in phase-3-result [:pattern-extraction :total-patterns]))
         (str "Clusters Found: " (get-in phase-3-result [:clustering :num-clusters]))
         (str "Archetypes Identified: " (count (get-in phase-3-result [:archetypes])))
         (str "Anomalies Detected: " (get-in phase-3-result [:anomalies :total-anomalies]))
         ""
         "Archetype Summary:"
         ""]]

    (let [with-archetypes
          (concat summary-lines
                  (for [[name archetype] (sort-by key (get-in phase-3-result [:archetypes]))]
                    (str "  " name ": " (:size archetype) " patterns, dominant leitmotif: " (:dominant-leitmotif archetype))))]

      (spit filepath (str/join "\n" with-archetypes)))))
