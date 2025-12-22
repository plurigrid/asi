(ns agents.phase-6-timeline-construction
  "Phase 6: Interaction Timeline Construction

   Constructs coherent interaction timelines from temporal patterns:
   - Timeline assembly from cluster sequences
   - Actor role identification
   - Event extraction and annotation
   - Timeline validation and consistency checking
   - Multi-scale timeline hierarchy

   Input: Temporal patterns from discovery module
   Output: Structured timelines with semantic annotations

   Status: 2025-12-21 - Timeline construction system"
  (:require [clojure.data.json :as json]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: Actor Role Identification
;; =============================================================================

(defn compute-actor-metrics
  \"Compute engagement metrics for each participant
   Input: cluster summaries
   Output: actor profiles\"
  [cluster-summaries]

  (let [;; Collect all actors and their participation
        actor-stats (reduce (fn [acc cluster]
                           (let [participants (:participants cluster)
                                 message-count (/ (:message-count cluster)
                                                (count participants))]

                             (reduce (fn [a participant]
                                    (update a participant
                                           (fn [stats]
                                             (-> (or stats
                                                    {:messages 0 :clusters 0 :words 0})
                                                (update :messages + 1)
                                                (update :clusters + 1)
                                                (update :words + (/ (:total-words cluster)
                                                                   (count participants)))))))
                                   acc
                                   participants)))
                        {}
                        cluster-summaries)

        ;; Classify actors by engagement level
        actor-profiles (into {}
                           (map (fn [[actor stats]]
                                [actor
                                 {:actor-id actor
                                  :message-count (:messages stats)
                                  :cluster-count (:clusters stats)
                                  :total-words (:words stats)
                                  :avg-words-per-message (/ (:words stats)
                                                            (:messages stats))
                                  :role (cond
                                        (> (:messages stats) 100) :core-contributor
                                        (> (:messages stats) 50) :frequent-contributor
                                        (> (:messages stats) 20) :regular-participant
                                        :else :occasional-participant)}])
                               actor-stats))]

    {:actor-profiles actor-profiles
     :core-contributors (count (filter #(= :core-contributor (:role (val %)))
                                      actor-profiles))
     :frequent-contributors (count (filter #(= :frequent-contributor (:role (val %)))
                                           actor-profiles))
     :total-actors (count actor-profiles)}))

;; =============================================================================
;; Section 2: Event Extraction
;; =============================================================================

(defn extract-events-from-cluster
  \"Extract discrete events from a temporal cluster
   Input: cluster summary
   Output: sequence of events\"
  [cluster-summary]

  (let [;; Major topic as primary event
        topics (:topics cluster-summary)
        streams (:streams cluster-summary)

        primary-topic (first topics)
        primary-stream (first streams)

        ;; Event intensity based on message volume
        intensity (cond
                  (> (:message-count cluster-summary) 100) :high
                  (> (:message-count cluster-summary) 50) :medium
                  :else :low)

        ;; Event type based on content
        event-type (case (:content-type cluster-summary)
                    :mathematical :technical-discussion
                    :technical :implementation-discussion
                    :referential :reference-sharing
                    :conversational :general-discussion)]

    {:event-type event-type
     :primary-topic primary-topic
     :primary-stream primary-stream
     :timestamp-start (:cluster-start cluster-summary)
     :timestamp-end (:cluster-end cluster-summary)
     :duration-minutes (:duration-minutes cluster-summary)
     :participant-count (:participant-count cluster-summary)
     :message-count (:message-count cluster-summary)
     :intensity intensity
     :participants (:participants cluster-summary)
     :all-topics (vec topics)}))

;; =============================================================================
;; Section 3: Timeline Assembly
;; =============================================================================

(defn assemble-timeline
  \"Assemble temporal events into coherent timeline
   Input: cluster summaries ordered by time
   Output: structured timeline\"
  [ordered-clusters]

  (let [;; Extract events in order
        events (vec (map extract-events-from-cluster ordered-clusters))

        ;; Compute event sequence statistics
        total-events (count events)
        total-duration (reduce + (map :duration-minutes events))
        total-participants (count (set (mapcat :participants events)))

        ;; Event transitions
        transitions (map vector events (rest events))

        ;; Compute gaps between events
        time-gaps (map (fn [[e1 e2]]
                       (/ (- (:timestamp-start e2)
                             (:timestamp-end e1))
                         60000.0))
                     transitions)

        avg-gap (if (seq time-gaps)
                (/ (reduce + time-gaps) (count time-gaps))
                0.0)

        ;; Identify event clusters (groups of related events)
        event-clusters (reduce (fn [acc event]
                              (let [last-cluster (peek acc)
                                   last-event (when last-cluster
                                             (peek last-cluster))
                                   time-gap (if last-event
                                           (- (:timestamp-start event)
                                             (:timestamp-end last-event))
                                           0)]

                                (if (and last-cluster (< time-gap (* 30 60 1000)))
                                 ;; Add to existing cluster (within 30 min)
                                 (conj (pop acc) (conj last-cluster event))
                                 ;; Start new cluster
                                 (conj acc [event]))))
                             []
                             events)]

    {:timeline
     {:events events
      :event-count total-events
      :event-clusters (count event-clusters)
      :total-duration-minutes total-duration
      :unique-participants total-participants
      :avg-gap-between-events avg-gap}

     :event-clusters event-clusters

     :temporal-span
     {:start-time (when (seq events) (:timestamp-start (first events)))
      :end-time (when (seq events) (:timestamp-end (last events)))}}))

;; =============================================================================
;; Section 4: Timeline Hierarchy
;; =============================================================================

(defn create-multi-scale-timeline
  \"Create hierarchical timeline at different scales
   Input: events
   Output: timelines at different granularities\"
  [events]

  (let [;; Group by time scale
        hourly (group-by (fn [event]
                         (quot (:timestamp-start event) (* 60 60 1000)))
                        events)

        daily (group-by (fn [event]
                        (quot (:timestamp-start event) (* 24 60 60 1000)))
                       events)

        weekly (group-by (fn [event]
                         (quot (:timestamp-start event) (* 7 24 60 60 1000)))
                        events)

        ;; Compute summary statistics for each scale
        hourly-summary (into {}
                          (map (fn [[hour events-in-hour]]
                               [hour {:event-count (count events-in-hour)
                                     :participant-count (count (set (mapcat :participants
                                                                          events-in-hour)))}])
                            hourly))

        daily-summary (into {}
                         (map (fn [[day events-in-day]]
                              [day {:event-count (count events-in-day)
                                   :participant-count (count (set (mapcat :participants
                                                                        events-in-day)))}])
                           daily))

        weekly-summary (into {}
                          (map (fn [[week events-in-week]]
                               [week {:event-count (count events-in-week)
                                     :participant-count (count (set (mapcat :participants
                                                                          events-in-week)))}])
                            weekly))]

    {:scales
     {:hourly {:groups hourly
              :summary hourly-summary
              :total-groups (count hourly)}

      :daily {:groups daily
             :summary daily-summary
             :total-groups (count daily)}

      :weekly {:groups weekly
              :summary weekly-summary
              :total-groups (count weekly)}}}))

;; =============================================================================
;; Section 5: Timeline Validation
;; =============================================================================

(defn validate-timeline
  \"Validate timeline for consistency and completeness
   Input: assembled timeline
   Output: validation report\"
  [timeline-struct]

  (let [events (get-in timeline-struct [:timeline :events])

        ;; Check: events are ordered by time
        is-ordered (every? true?
                         (map (fn [[e1 e2]]
                             (<= (:timestamp-start e1)
                                (:timestamp-start e2)))
                            (map vector events (rest events))))

        ;; Check: no time gaps are negative
        no-negative-gaps (every? #(>= % 0.0)
                               (map (fn [[e1 e2]]
                                   (- (:timestamp-start e2)
                                     (:timestamp-end e1)))
                                (map vector events (rest events))))

        ;; Check: participant counts are consistent
        valid-participants (every? #(> (:participant-count %) 0)
                                  events)

        ;; Check: duration is reasonable
        valid-duration (every? #(>= (:duration-minutes %) 0)
                             events)

        ;; Overall validity
        is-valid (and is-ordered no-negative-gaps valid-participants valid-duration)]

    {:is-valid is-valid
     :events-ordered is-ordered
     :no-negative-gaps no-negative-gaps
     :participants-valid valid-participants
     :duration-valid valid-duration
     :event-count (count events)
     :validation-status (if is-valid :passed :failed)}))

;; =============================================================================
;; Section 6: Timeline Annotation
;; =============================================================================

(defn annotate-timeline-with-concepts
  \"Annotate timeline events with mathematical/technical concepts
   Input: events, concept registry
   Output: annotated events\"
  [events]

  (let [concept-keywords {"functor" :category-theory
                         "morphism" :category-theory
                         "adjoint" :category-theory
                         "monad" :functional-programming
                         "comonad" :functional-programming
                         "proof" :logic
                         "theorem" :logic
                         "cohomology" :algebraic-topology
                         "homology" :algebraic-topology
                         "sheaf" :algebraic-geometry}

        annotated-events (map (fn [event]
                             (let [all-topics (str/join " " (:all-topics event))
                                  topic-lower (str/lower-case all-topics)

                                  detected-concepts
                                  (set (for [[keyword concept] concept-keywords
                                            :when (str/includes? topic-lower keyword)]
                                       concept))]

                               (assoc event
                                     :detected-concepts (vec detected-concepts)
                                     :semantic-type (cond
                                                    (seq detected-concepts) :technical
                                                    :else :general))))
                            events)]

    annotated-events))

;; =============================================================================
;; Section 7: Timeline Summary
;; =============================================================================

(defn generate-timeline-summary
  \"Generate human-readable timeline summary
   Input: assembled timeline
   Output: summary text\"
  [timeline-struct]

  (let [timeline (:timeline timeline-struct)
        events (:events timeline)
        event-clusters (:event-clusters timeline-struct)]

    {:summary-text
     (str "Timeline Analysis Summary\n"
         "═══════════════════════════════════════════════════════\n\n"
         "📊 TIMELINE OVERVIEW\n"
         "  Total events: " (:event-count timeline) "\n"
         "  Total duration: " (:total-duration-minutes timeline) " minutes\n"
         "  Unique participants: " (:unique-participants timeline) "\n"
         "  Event clusters: " (:event-clusters timeline) "\n"
         "  Average gap between events: " (format "%.1f" (:avg-gap-between-events timeline)) " minutes\n\n"

         "🎯 EVENT DISTRIBUTION\n"
         "  High intensity events: " (count (filter #(= :high (:intensity %)) events)) "\n"
         "  Medium intensity events: " (count (filter #(= :medium (:intensity %)) events)) "\n"
         "  Low intensity events: " (count (filter #(= :low (:intensity %)) events)) "\n\n"

         "🔍 DOMINANT TOPICS\n"
         (str/join "\n"
                  (map (fn [[topic count]]
                       (str "  " topic ": " count " events"))
                      (take 5 (reverse (sort-by val (frequencies (mapcat :all-topics events)))))))
         "\n")

     :validation (:is-valid (validate-timeline timeline-struct))
     :event-count (:event-count timeline)
     :duration-minutes (:total-duration-minutes timeline)}))

;; =============================================================================
;; Section 8: Export Timeline
;; =============================================================================

(defn export-timeline-to-json
  \"Export timeline to JSON format
   Input: assembled timeline
   Output: JSON-serializable structure\"
  [timeline-struct]

  (let [timeline (:timeline timeline-struct)
        events (:events timeline)]

    {:timeline
     {:metadata
      {:event-count (:event-count timeline)
       :total-duration-minutes (:total-duration-minutes timeline)
       :unique-participants (:unique-participants timeline)
       :event-clusters (:event-clusters timeline)}

      :events (vec (map (fn [event]
                       {:type (:event-type event)
                        :topic (:primary-topic event)
                        :duration-minutes (:duration-minutes event)
                        :participants (:participant-count event)
                        :messages (:message-count event)
                        :intensity (name (:intensity event))})
                      events))}}))

;; =============================================================================
;; Section 9: Main Assembly Pipeline
;; =============================================================================

(defn construct-interaction-timeline
  \"Main pipeline for timeline construction
   Input: temporal patterns from discovery module
   Output: complete structured timeline\"
  [cluster-summaries]

  (println \"\\n╔══════════════════════════════════════════════════════════╗\")
  (println \"║  PHASE 6: INTERACTION TIMELINE CONSTRUCTION              ║\")
  (println \"╚══════════════════════════════════════════════════════════╝\\n\")

  ;; Sort clusters by time
  (let [ordered-clusters (sort-by :cluster-start cluster-summaries)

        ;; Compute actor metrics
        actors (compute-actor-metrics ordered-clusters)

        ;; Assemble timeline
        timeline-struct (assemble-timeline ordered-clusters)

        ;; Create multi-scale view
        multi-scale (create-multi-scale-timeline
                    (get-in timeline-struct [:timeline :events]))

        ;; Validate
        validation (validate-timeline timeline-struct)

        ;; Annotate with concepts
        annotated-events (annotate-timeline-with-concepts
                         (get-in timeline-struct [:timeline :events]))

        ;; Generate summary
        summary (generate-timeline-summary timeline-struct)

        ;; Export
        export (export-timeline-to-json timeline-struct)]

    ;; Print results
    (println \"👥 ACTOR ANALYSIS\")
    (println \"─────────────────────────────────────────────────────────\")
    (printf \"  Core contributors: %d%n\" (:core-contributors actors))
    (printf \"  Frequent contributors: %d%n\" (:frequent-contributors actors))
    (printf \"  Total participants: %d%n\" (:total-actors actors))

    (println \"\\n📅 TIMELINE STATISTICS\")
    (println \"─────────────────────────────────────────────────────────\")
    (printf \"  Total events: %d%n\" (get-in timeline-struct [:timeline :event-count]))
    (printf \"  Event clusters: %d%n\" (get-in timeline-struct [:timeline :event-clusters]))
    (printf \"  Avg gap between events: %.1f minutes%n\"
           (get-in timeline-struct [:timeline :avg-gap-between-events]))

    (println \"\\n✅ VALIDATION\")
    (println \"─────────────────────────────────────────────────────────\")
    (println (str \"  Status: \" (name (:validation-status validation))))
    (printf \"  Events ordered: %s%n\" (:events-ordered validation))
    (printf \"  No negative gaps: %s%n\" (:no-negative-gaps validation))

    (println \"\\n✅ TIMELINE CONSTRUCTION COMPLETE\")

    {:actor-profiles (:actor-profiles actors)
     :timeline-structure timeline-struct
     :multi-scale-view multi-scale
     :validation validation
     :annotated-events annotated-events
     :summary summary
     :export export}))
