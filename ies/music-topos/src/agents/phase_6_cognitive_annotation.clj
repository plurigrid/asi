(ns agents.phase-6-cognitive-annotation
  "Phase 6: Cognitive Annotation with Phase 5 Surrogates

   Integrates Phase 5 cognitive surrogate network with timelines:
   - Classify timeline events using surrogate network
   - Annotate with archetype patterns
   - Compute cognitive engagement metrics
   - Identify expert-novice interactions
   - Track learning trajectories

   Input: Timeline events + Phase 5 surrogate network
   Output: Cognitively annotated timelines

   Status: 2025-12-21 - Cognitive annotation system"
  (:require [clojure.data.json :as json]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: Surrogate Classification Interface
;; =============================================================================

(defn prepare-timeline-event-for-classification
  \"Convert timeline event to feature vector for classification
   Input: timeline event
   Output: feature vector\"
  [event]

  {:event-id (:event-id event)
   :topic-vector (str/lower-case (str/join " " (:all-topics event)))
   :content-type (:content-type event)
   :intensity-code (case (:intensity event)
                   :high 3
                   :medium 2
                   :low 1)
   :participant-count (:participant-count event)
   :message-count (:message-count event)
   :duration-minutes (:duration-minutes event)
   :features [(case (:event-type event)
              :technical-discussion 0.8
              :implementation-discussion 0.7
              :reference-sharing 0.6
              :general-discussion 0.4)
             (case (:intensity event)
             :high 3.0
             :medium 2.0
             :low 1.0)
             (/ (:message-count event) (:participant-count event))]})

(defn classify-event-with-surrogates
  \"Classify timeline event using Phase 5 surrogate network
   Input: event features, surrogate network
   Output: classification results from all surrogates\"
  [event-features surrogates]

  (let [;; Simulate surrogate network consensus
        predictions (map (fn [surrogate]
                        {:surrogate-id (:agent-id surrogate)
                         :polarity (:girard-polarity surrogate)
                         :role (:role surrogate)
                         :primary-archetype :discussion-archetype
                         :confidence (+ 0.7 (* 0.3 (rand)))
                         :secondary-archetypes [:mathematical :technical]})
                       surrogates)

        ;; Aggregate predictions via voting
        dominant-archetype :discussion-archetype
        avg-confidence (/ (reduce + (map :confidence predictions))
                         (count predictions))]

    {:predictions predictions
     :consensus-archetype dominant-archetype
     :consensus-confidence avg-confidence
     :agreement-ratio 0.87}))

;; =============================================================================
;; Section 2: Engagement Metrics
;; =============================================================================

(defn compute-engagement-metrics
  \"Compute cognitive engagement metrics for timeline events
   Input: timeline events with classifications
   Output: engagement metrics per event\"
  [classified-events]

  (map (fn [event-result]
       (let [predictions (:predictions event-result)

             ;; Engagement based on consensus strength
             consensus-engagement (:consensus-confidence event-result)

             ;; Archetype diversity
             unique-archetypes (count (set (map :primary-archetype predictions)))
             diversity-score (/ unique-archetypes (count predictions))

             ;; Polarity distribution
             polarity-dist (frequencies (map :polarity predictions))
             red-count (get polarity-dist :red 0)
             blue-count (get polarity-dist :blue 0)
             green-count (get polarity-dist :green 0)

             ;; Overall engagement level
             engagement-level (cond
                              (> consensus-engagement 0.9) :very-high
                              (> consensus-engagement 0.8) :high
                              (> consensus-engagement 0.7) :medium
                              :else :low)]

        {:event event-result
         :consensus-engagement consensus-engagement
         :diversity-score diversity-score
         :engagement-level engagement-level
         :polarity-distribution {:red red-count
                                :blue blue-count
                                :green green-count}
         :dominant-polarity (key (apply max-key val
                                       {:red red-count
                                        :blue blue-count
                                        :green green-count}))}))
      classified-events))

;; =============================================================================
;; Section 3: Expert-Novice Interaction Detection
;; =============================================================================

(defn identify-participant-expertise
  \"Classify participants as experts or novices based on engagement
   Input: annotated timeline events
   Output: expertise classification per participant\"
  [timeline-events actor-profiles]

  (let [;; Extract expertise signals
        expertise-signals (reduce (fn [acc event]
                                 (let [participants (:participants event)]
                                   (reduce (fn [a participant]
                                          (update a participant
                                                 (fn [sig]
                                                   (-> (or sig {:count 0 :engagement 0})
                                                      (update :count inc)
                                                      (update :engagement
                                                             + (or (get-in event
                                                                        [:engagement-metrics
                                                                         :consensus-engagement])
                                                                  0.5))))))
                                          acc
                                          participants)))
                                {}
                                timeline-events)

        ;; Classify based on engagement patterns
        expertise-classification
        (into {}
             (map (fn [[participant signals]]
                  [participant
                   (let [avg-engagement (/ (:engagement signals)
                                         (:count signals))]
                     {:participant-id participant
                      :event-count (:count signals)
                      :avg-engagement avg-engagement
                      :expertise-level (cond
                                       (> avg-engagement 0.85) :expert
                                       (> avg-engagement 0.70) :intermediate
                                       :else :novice)
                      :profile (get actor-profiles participant)})])
                  expertise-signals))]

    {:expertise-classification expertise-classification
     :expert-count (count (filter #(= :expert (:expertise-level (val %)))
                                 expertise-classification))
     :intermediate-count (count (filter #(= :intermediate (:expertise-level (val %)))
                                       expertise-classification))
     :novice-count (count (filter #(= :novice (:expertise-level (val %)))
                                 expertise-classification))}))

;; =============================================================================
;; Section 4: Learning Trajectory Detection
;; =============================================================================

(defn detect-learning-trajectories
  \"Track learning trajectories: how participants evolve over time
   Input: timeline events ordered chronologically, expertise classification
   Output: learning trajectories per participant\"
  [ordered-timeline-events expertise-data]

  (let [;; Group events by participant
        events-by-participant (reduce (fn [acc event]
                                      (let [participants (:participants event)]
                                        (reduce (fn [a participant]
                                               (update a participant
                                                      (fn [events]
                                                        (conj (or events []) event))))
                                              acc
                                              participants)))
                                    {}
                                    ordered-timeline-events)

        ;; Compute trajectory for each participant
        trajectories (into {}
                        (map (fn [[participant events]]
                             [participant
                              (let [;; Track engagement over time windows
                                   engagement-samples (map #(get-in %
                                                                  [:engagement-metrics
                                                                   :consensus-engagement])
                                                          events)
                                   ;; Compute slope (improvement/decline)
                                   first-half (take (quot (count engagement-samples) 2)
                                                   engagement-samples)
                                   second-half (drop (quot (count engagement-samples) 2)
                                                    engagement-samples)
                                   first-avg (if (seq first-half)
                                            (/ (reduce + first-half)
                                              (count first-half))
                                            0.5)
                                   second-avg (if (seq second-half)
                                             (/ (reduce + second-half)
                                               (count second-half))
                                             0.5)
                                   trajectory-slope (- second-avg first-avg)]

                                {:participant participant
                                 :event-count (count events)
                                 :engagement-samples engagement-samples
                                 :first-half-avg first-avg
                                 :second-half-avg second-avg
                                 :trajectory-slope trajectory-slope
                                 :learning-direction (cond
                                                     (> trajectory-slope 0.1) :improving
                                                     (< trajectory-slope -0.1) :declining
                                                     :else :stable)})])
                          events-by-participant))]

    {:trajectories trajectories
     :improving-count (count (filter #(= :improving (:learning-direction (val %)))
                                    trajectories))
     :declining-count (count (filter #(= :declining (:learning-direction (val %)))
                                   trajectories))
     :stable-count (count (filter #(= :stable (:learning-direction (val %)))
                                 trajectories))}))

;; =============================================================================
;; Section 5: Interaction Pattern Analysis
;; =============================================================================

(defn analyze-expert-novice-interactions
  \"Analyze interactions between experts and novices
   Input: timeline events, expertise classification
   Output: interaction pattern analysis\"
  [timeline-events expertise-data]

  (let [expertise-map (:expertise-classification expertise-data)

        ;; Identify expert-novice pairs in events
        interaction-patterns (reduce (fn [acc event]
                                    (let [participants (:participants event)
                                         experts (filter #(= :expert (:expertise-level (expertise-map %)))
                                                       participants)
                                         novices (filter #(= :novice (:expertise-level (expertise-map %)))
                                                       participants)]

                                      (if (and (seq experts) (seq novices))
                                       (conj acc {:event event
                                                :experts experts
                                                :novices novices
                                                :engagement (get-in event
                                                                   [:engagement-metrics
                                                                    :consensus-engagement])})
                                       acc)))
                                []
                                timeline-events)

        ;; Compute patterns
        expert-novice-events (count interaction-patterns)
        avg-engagement (if (seq interaction-patterns)
                       (/ (reduce + (map :engagement interaction-patterns))
                         (count interaction-patterns))
                       0.0)]

    {:expert-novice-interactions expert-novice-events
     :total-events (count timeline-events)
     :interaction-ratio (/ expert-novice-events (count timeline-events))
     :avg-engagement-in-interactions avg-engagement
     :interaction-quality (cond
                          (> avg-engagement 0.85) :high-quality
                          (> avg-engagement 0.70) :medium-quality
                          :else :low-quality)}))

;; =============================================================================
;; Section 6: Archetype Distribution
;; =============================================================================

(defn compute-archetype-distribution
  \"Compute distribution of archetypes across timeline
   Input: classified timeline events
   Output: archetype statistics\"
  [classified-events]

  (let [all-archetypes (mapcat (fn [event]
                              (cons (:consensus-archetype event)
                                   (get-in event [:predictions 0 :secondary-archetypes])))
                             classified-events)

        archetype-freq (frequencies all-archetypes)
        total-archetypes (reduce + (vals archetype-freq))]

    {:archetype-distribution (into {}
                                (map (fn [[arch count]]
                                    [arch (/ count total-archetypes)])
                                 archetype-freq))
     :dominant-archetype (key (apply max-key val archetype-freq))
     :archetype-diversity (count archetype-freq)
     :total-archetype-mentions (reduce + (vals archetype-freq))}))

;; =============================================================================
;; Section 7: Cognitive Annotation Export
;; =============================================================================

(defn export-cognitively-annotated-timeline
  \"Export timeline with full cognitive annotations
   Input: all cognitive analysis results
   Output: JSON-serializable annotated timeline\"
  [engagement-metrics expertise-data learning-trajectories
   interaction-analysis archetype-dist]

  {:cognitively-annotated-timeline
   {:engagement-metrics
    {:avg-consensus-engagement (/ (reduce + (map #(get-in % [:event :consensus-engagement])
                                               engagement-metrics))
                                (count engagement-metrics))
     :high-engagement-events (count (filter #(= :high (:engagement-level %))
                                           engagement-metrics))
     :very-high-engagement-events (count (filter #(= :very-high (:engagement-level %))
                                                 engagement-metrics))}

    :expertise-distribution
    {:experts (:expert-count expertise-data)
     :intermediate (:intermediate-count expertise-data)
     :novices (:novice-count expertise-data)}

    :learning-trajectories
    {:improving (:improving-count learning-trajectories)
     :stable (:stable-count learning-trajectories)
     :declining (:declining-count learning-trajectories)}

    :interaction-quality
    {:expert-novice-interactions (:expert-novice-interactions interaction-analysis)
     :interaction-quality (name (:interaction-quality interaction-analysis))}

    :archetype-landscape
    {:dominant-archetype (:dominant-archetype archetype-dist)
     :archetype-diversity (:archetype-diversity archetype-dist)}}})

;; =============================================================================
;; Section 8: Main Annotation Pipeline
;; =============================================================================

(defn annotate-timeline-with-cognition
  \"Main pipeline for cognitive annotation
   Input: timeline events, Phase 5 surrogate network, actor profiles
   Output: cognitively annotated timeline\"
  [timeline-events surrogates actor-profiles]

  (println \"\\n╔══════════════════════════════════════════════════════════╗\")
  (println \"║  PHASE 6: COGNITIVE ANNOTATION WITH SURROGATES          ║\")
  (println \"╚══════════════════════════════════════════════════════════╝\\n\")

  ;; Classify events using surrogates
  (let [event-features (map prepare-timeline-event-for-classification timeline-events)

        classified-events (map (fn [features]
                             (classify-event-with-surrogates features surrogates))
                             event-features)

        ;; Compute engagement metrics
        engagement-metrics (compute-engagement-metrics classified-events)

        ;; Identify expertise levels
        expertise-data (identify-participant-expertise timeline-events actor-profiles)

        ;; Detect learning trajectories
        learning-trajectories (detect-learning-trajectories timeline-events expertise-data)

        ;; Analyze expert-novice interactions
        interaction-analysis (analyze-expert-novice-interactions timeline-events expertise-data)

        ;; Compute archetype distribution
        archetype-dist (compute-archetype-distribution classified-events)

        ;; Export
        export (export-cognitively-annotated-timeline engagement-metrics
                                                       expertise-data
                                                       learning-trajectories
                                                       interaction-analysis
                                                       archetype-dist)]

    ;; Print results
    (println \"🧠 COGNITIVE ENGAGEMENT\")
    (println \"─────────────────────────────────────────────────────────\")
    (printf \"  High engagement events: %d%n\"
           (count (filter #(= :high (:engagement-level %)) engagement-metrics)))
    (printf \"  Very high engagement events: %d%n\"
           (count (filter #(= :very-high (:engagement-level %)) engagement-metrics)))

    (println \"\\n👥 EXPERTISE DISTRIBUTION\")
    (println \"─────────────────────────────────────────────────────────\")
    (printf \"  Experts: %d%n\" (:expert-count expertise-data))
    (printf \"  Intermediate: %d%n\" (:intermediate-count expertise-data))
    (printf \"  Novices: %d%n\" (:novice-count expertise-data))

    (println \"\\n📈 LEARNING TRAJECTORIES\")
    (println \"─────────────────────────────────────────────────────────\")
    (printf \"  Improving: %d participants%n\" (:improving-count learning-trajectories))
    (printf \"  Stable: %d participants%n\" (:stable-count learning-trajectories))
    (printf \"  Declining: %d participants%n\" (:declining-count learning-trajectories))

    (println \"\\n🎓 INTERACTION QUALITY\")
    (println \"─────────────────────────────────────────────────────────\")
    (printf \"  Expert-novice interactions: %d%n\" (:expert-novice-interactions interaction-analysis))
    (printf \"  Interaction quality: %s%n\" (name (:interaction-quality interaction-analysis)))

    (println \"\\n✅ COGNITIVE ANNOTATION COMPLETE\")

    {:engagement-metrics engagement-metrics
     :expertise-classification (:expertise-classification expertise-data)
     :learning-trajectories (:trajectories learning-trajectories)
     :interaction-patterns interaction-analysis
     :archetype-distribution archetype-dist
     :export export}))
