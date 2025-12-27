(ns agents.entropy-metrics
  "Interaction Entropy Metrics & Mode Collapse Prevention

  Prevents mode collapse in agent-o-rama training by monitoring
  5-dimensional entropy and detecting when model diversity collapses.

  Status: 2025-12-21 - Phase 3→4 integration ready"
  (:require [clojure.math :as math]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: Shannon Entropy Calculation
;; =============================================================================

(defn shannon-entropy
  "Calculate Shannon entropy of a distribution
   H = -Σ(p_i * log(p_i)) where p_i are proportions"
  [values]
  (let [total (count values)
        counts (frequencies values)
        proportions (map #(/ % total) (vals counts))
        entropy (- (reduce + (map #(* % (math/log %))
                                 (filter #(> % 0) proportions))))]
    (/ entropy (math/log 2))))  ; Convert to bits

;; =============================================================================
;; Section 2: Topic Entropy
;; =============================================================================

(def ^:dynamic *topic-keywords*
  "Keywords to classify posts into topics"
  {:tech ["code" "clojure" "programming" "api" "database" "algorithm"]
   :music ["music" "sound" "overtone" "synthesis" "rhythm" "beat"]
   :philosophy ["meaning" "consciousness" "identity" "perception" "being"]
   :math ["topos" "category" "functor" "algebra" "geometry" "proof"]
   :ai ["agent" "learning" "model" "train" "neural" "gpt"]
   :network ["connect" "graph" "node" "edge" "relationship" "protocol"]
   :personal ["thought" "feeling" "experience" "observation" "reflection"]
   :community ["collaboration" "team" "group" "project" "contribute"]})

(defn extract-topics
  "Extract topics from post content using keyword matching"
  [posts]
  (let [keywords-lower (update-vals *topic-keywords* #(map str/lower-case %))]
    (map (fn [post]
           (let [content (str/lower-case (get post :content ""))
                 matched-topics (for [[topic kws] keywords-lower
                                     :when (some #(str/includes? content %) kws)]
                                 topic)]
             (if (seq matched-topics)
               (first matched-topics)  ; Primary topic
               :other)))
         posts)))

(defn calculate-topic-entropy
  "Measure diversity of topics discussed"
  [posts]
  (let [topics (extract-topics posts)
        entropy (shannon-entropy topics)]
    {:topic-entropy entropy
     :distribution (frequencies topics)
     :interpretation (cond
                       (>= entropy 3.5) "Highly diverse topics"
                       (>= entropy 2.5) "Good topic variety"
                       (>= entropy 1.5) "Limited topic range"
                       :else "Focused on few topics (low diversity)")}))

;; =============================================================================
;; Section 3: Interaction Mode Entropy
;; =============================================================================

(def interaction-modes
  {:original "Original thought/content creation"
   :reply "Response to others"
   :quote "Commentary/remixing"
   :thread "Extended thought thread"
   :mention "Direct connection/attribution"
   :collaboration "Joint work/project"})

(defn infer-interaction-mode
  "Infer interaction mode from post structure"
  [post]
  (cond
    (:in-reply-to post) :reply
    (:quoted post) :quote
    (:thread-continuation post) :thread
    (:mentions post) (if (:mentions-count post) :mention :original)
    (:collaborators post) :collaboration
    :else :original))

(defn calculate-mode-entropy
  "Measure diversity of interaction types"
  [posts]
  (let [modes (map infer-interaction-mode posts)
        entropy (shannon-entropy modes)
        distribution (frequencies modes)
        total (count modes)
        proportions (update-vals distribution #(double (/ % total)))]
    {:mode-entropy entropy
     :distribution proportions
     :expected-healthy {:original 0.25-0.35
                       :reply 0.35-0.45
                       :quote 0.10-0.15
                       :thread 0.05-0.10
                       :mention 0.05-0.10
                       :collaboration 0.05-0.10}
     :interpretation (cond
                       (>= entropy 2.4) "Balanced interaction modes"
                       (>= entropy 1.8) "Reasonably diverse modes"
                       (>= entropy 1.2) "Limited mode variety"
                       :else "Dominated by single mode (collapse risk)")}))

;; =============================================================================
;; Section 4: Temporal Entropy
;; =============================================================================

(defn calculate-temporal-entropy
  "Measure unpredictability of posting patterns"
  [posts]
  (let [sorted-posts (sort-by :timestamp posts)
        timestamps (map :timestamp sorted-posts)
        intervals (map - (rest timestamps) timestamps)

        ;; Bucket intervals into time ranges
        bucketed (map (fn [interval]
                       (cond
                         (< interval 300000) :5min           ; < 5 minutes
                         (< interval 3600000) :1hour         ; < 1 hour
                         (< interval 86400000) :1day         ; < 1 day
                         (< interval 604800000) :1week       ; < 1 week
                         :else :over-week))
                     intervals)

        entropy (shannon-entropy bucketed)
        distribution (frequencies bucketed)]

    {:temporal-entropy entropy
     :distribution distribution
     :num-posts (count posts)
     :time-span-ms (- (last timestamps) (first timestamps))
     :interpretation (cond
                       (>= entropy 2.0) "Highly unpredictable posting times"
                       (>= entropy 1.4) "Reasonably varied posting patterns"
                       (>= entropy 0.8) "Some patterns in posting times"
                       :else "Highly predictable/regular posting (potential collapse)")}))

;; =============================================================================
;; Section 5: Network Entropy
;; =============================================================================

(defn calculate-network-entropy
  "Measure diversity of network connections"
  [network-relationships]
  (let [out-degrees (map count (group-by :source network-relationships))
        in-degrees (map count (group-by :target network-relationships))

        ;; Degree distribution entropy
        out-entropy (shannon-entropy out-degrees)
        in-entropy (shannon-entropy in-degrees)
        avg-entropy (/ (+ out-entropy in-entropy) 2)

        num-unique-sources (count (set (map :source network-relationships)))
        num-unique-targets (count (set (map :target network-relationships)))]

    {:network-entropy avg-entropy
     :out-entropy out-entropy
     :in-entropy in-entropy
     :num-unique-sources num-unique-sources
     :num-unique-targets num-unique-targets
     :out-degree-distribution (frequencies out-degrees)
     :in-degree-distribution (frequencies in-degrees)
     :interpretation (cond
                       (>= avg-entropy 3.5) "Very diverse network (many connections)"
                       (>= avg-entropy 2.5) "Good network diversity"
                       (>= avg-entropy 1.5) "Limited network interactions"
                       :else "Insular network (collapse risk - same people)")}))

;; =============================================================================
;; Section 6: Content Length Entropy
;; =============================================================================

(defn calculate-length-entropy
  "Measure diversity in expression length"
  [posts]
  (let [lengths (map #(count (get % :content "")) posts)

        ;; Bucket into quantile-based bins
        bucketed (map (fn [len]
                       (cond
                         (< len 50) :micro       ; <50 chars
                         (< len 280) :short      ; <280 chars (tweet-like)
                         (< len 1000) :medium    ; <1000 chars
                         (< len 5000) :long      ; <5000 chars
                         :else :essay))          ; >5000 chars
                     lengths)

        entropy (shannon-entropy bucketed)
        distribution (frequencies bucketed)
        total (count lengths)
        proportions (update-vals distribution #(double (/ % total)))]

    {:length-entropy entropy
     :distribution proportions
     :min-length (apply min lengths)
     :max-length (apply max lengths)
     :mean-length (double (/ (reduce + lengths) (count lengths)))
     :interpretation (cond
                       (>= entropy 1.8) "Good variety in expression lengths"
                       (>= entropy 1.2) "Some variety in post length"
                       (>= entropy 0.6) "Mostly similar lengths (collapse risk)"
                       :else "All posts very similar length")}))

;; =============================================================================
;; Section 7: Composite Entropy Score
;; =============================================================================

(defn calculate-all-entropies
  "Calculate all 5 entropy dimensions for a dataset"
  [posts interactions network-relationships]
  (let [topic-ent (calculate-topic-entropy posts)
        mode-ent (calculate-mode-entropy interactions)
        temporal-ent (calculate-temporal-entropy posts)
        network-ent (calculate-network-entropy network-relationships)
        length-ent (calculate-length-entropy posts)

        entropies [(:topic-entropy topic-ent)
                  (:mode-entropy mode-ent)
                  (:temporal-entropy temporal-ent)
                  (:network-entropy network-ent)
                  (:length-entropy length-ent)]

        mean-entropy (double (/ (reduce + entropies) (count entropies)))
        max-entropy (apply max entropies)
        min-entropy (apply min entropies)
        variance (reduce + (map #(* (- % mean-entropy) (- % mean-entropy)) entropies))]

    {:topic topic-ent
     :mode mode-ent
     :temporal temporal-ent
     :network network-ent
     :length length-ent

     :composite {:mean-entropy mean-entropy
                 :max-entropy max-entropy
                 :min-entropy min-entropy
                 :variance variance}

     :overall-health (cond
                       (and (>= mean-entropy 2.7) (< variance 0.3)) :excellent
                       (and (>= mean-entropy 2.5) (< variance 0.5)) :good
                       (and (>= mean-entropy 2.2) (< variance 0.8)) :fair
                       (>= mean-entropy 1.8) :at-risk
                       :else :collapse-likely)}))

;; =============================================================================
;; Section 8: Mode Collapse Detection
;; =============================================================================

(defn entropy-slope
  "Calculate slope of entropy decline (for collapse detection)"
  [entropy-history window-size]
  (let [recent (take-last window-size entropy-history)
        early (take-first window-size entropy-history)

        recent-avg (/ (reduce + (map :mean-entropy recent)) (count recent))
        early-avg (/ (reduce + (map :mean-entropy early)) (count early))

        slope (/ (- recent-avg early-avg) (count early))]
    slope))

(defn detect-collapse-risk
  "Detect if mode collapse is occurring based on entropy history"
  [entropy-history]
  (let [recent-10 (take-last 10 entropy-history)
        early-10 (take-first 10 entropy-history)

        early-mean (/ (reduce + (map #(get-in % [:composite :mean-entropy]) early-10)) 10)
        recent-mean (/ (reduce + (map #(get-in % [:composite :mean-entropy]) recent-10)) 10)

        slope (/ (- recent-mean early-mean) 10)

        ;; Individual metric collapse
        topic-declining (< (slope 0) -0.15)
        mode-declining (< (slope 1) -0.12)
        temporal-declining (< (slope 2) -0.15)
        network-declining (< (slope 3) -0.15)]

    {:is-collapsing? (< slope -0.1)
     :slope slope
     :early-avg early-mean
     :recent-avg recent-mean
     :metrics-collapsing {:topic topic-declining
                         :mode mode-declining
                         :temporal temporal-declining
                         :network network-declining}

     :risk-level (cond
                   (< slope -0.2) :critical
                   (< slope -0.1) :high
                   (< slope -0.05) :medium
                   :else :low)

     :recommendation (cond
                       (< slope -0.2) "URGENT: Restore from checkpoint, reduce learning rate 10x"
                       (< slope -0.1) "WARNING: Monitor closely, consider reducing learning rate 5x"
                       (< slope -0.05) "CAUTION: Entropy declining, increase diversity loss weight"
                       :else "OK: Entropy stable, continue training")}))

;; =============================================================================
;; Section 9: Checkpoint Management
;; =============================================================================

(defn create-checkpoint
  "Create training checkpoint with entropy metrics"
  [epoch model generated-data training-data]
  (let [entropies (calculate-all-entropies
                   generated-data
                   (:interactions generated-data)
                   (:network generated-data))]

    {:epoch epoch
     :timestamp (System/currentTimeMillis)
     :model model
     :entropy-metrics entropies
     :overall-health (:overall-health entropies)
     :metadata {:num-samples (count generated-data)
               :model-parameters-count (atom 0)}  ; Placeholder
     }))

(defn should-save-checkpoint?
  "Determine if checkpoint should be saved"
  [current previous-best threshold]
  (let [current-entropy (get-in current [:entropy-metrics :composite :mean-entropy])
        previous-entropy (get-in previous-best [:entropy-metrics :composite :mean-entropy])]

    (> current-entropy (+ previous-entropy threshold))))

;; =============================================================================
;; Section 10: Training Loss with Diversity
;; =============================================================================

(defn diversity-loss
  "Calculate diversity loss penalty for training
   Encourages high entropy, penalizes collapse"
  [generated-entropies target-entropies lambda]
  (let [entropy-diff (- (get-in target-entropies [:composite :mean-entropy])
                       (get-in generated-entropies [:composite :mean-entropy]))

        penalty (* lambda (Math/abs entropy-diff))]

    {:diversity-loss penalty
     :entropy-gap entropy-diff
     :is-penalized (< entropy-diff -0.1)}))

(defn combined-loss
  "Total training loss = reconstruction + diversity penalty"
  [reconstruction-loss diversity-loss-value]
  (+ reconstruction-loss diversity-loss-value))

;; =============================================================================
;; Section 11: Display Functions
;; =============================================================================

(defn display-entropy-report
  "Display formatted entropy metrics"
  [entropy-metrics epoch]
  (println "\n" (str "Epoch " epoch " | Entropy Report"))
  (println "─────────────────────────────────────────────────────")

  (let [topic (get-in entropy-metrics [:topic :topic-entropy])
        mode (get-in entropy-metrics [:mode :mode-entropy])
        temporal (get-in entropy-metrics [:temporal :temporal-entropy])
        network (get-in entropy-metrics [:network :network-entropy])
        length (get-in entropy-metrics [:length :length-entropy])
        mean (get-in entropy-metrics [:composite :mean-entropy])
        health (:overall-health entropy-metrics)]

    (printf "Topic:    %.2f bits | " topic)
    (println (if (>= topic 3.5) "✅" "⚠️"))

    (printf "Mode:     %.2f bits | " mode)
    (println (if (>= mode 2.3) "✅" "⚠️"))

    (printf "Temporal: %.2f bits | " temporal)
    (println (if (>= temporal 1.8) "✅" "⚠️"))

    (printf "Network:  %.2f bits | " network)
    (println (if (>= network 3.2) "✅" "⚠️"))

    (printf "Length:   %.2f bits | " length)
    (println (if (>= length 1.5) "✅" "⚠️"))

    (println "─────────────────────────────────────────────────────")
    (printf "Average:  %.2f bits | Health: %s\n" mean
           (case health
             :excellent "🟢 Excellent"
             :good "🟢 Good"
             :fair "🟡 Fair"
             :at-risk "🟠 At Risk"
             :collapse-likely "🔴 Collapse Risk"))))

(defn display-collapse-warning
  "Display mode collapse warning"
  [collapse-info]
  (let [{:keys [is-collapsing? slope risk-level recommendation]} collapse-info]
    (when is-collapsing?
      (println "\n⚠️  MODE COLLAPSE DETECTED!")
      (println (str "  Entropy slope: " (format "%.4f" slope)))
      (println (str "  Risk level: " (str/upper-case (str risk-level))))
      (println (str "  Recommendation: " recommendation)))))

;; =============================================================================
;; End of module
;; =============================================================================
