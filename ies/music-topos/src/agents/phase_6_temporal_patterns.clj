(ns agents.phase-6-temporal-patterns
  "Phase 6: Temporal Pattern Discovery from Message History

   Discovers temporal patterns in Zulip message sequences:
   - Message thread reconstruction
   - Temporal clustering (conversations)
   - Participant interaction sequences
   - Pattern frequency analysis
   - Causal relationship extraction

   Input: Category Theory Zulip message archive (123,614 messages)
   Output: Temporal patterns with clustering

   Status: 2025-12-21 - Temporal discovery system"
  (:require [clojure.data.json :as json]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: Message Data Structures
;; =============================================================================

(defn create-message-record
  \"Create structured record from Zulip message
   Input: raw message data
   Output: normalized message record\"
  [message-id sender-id timestamp content topic stream]

  {:message-id message-id
   :sender-id sender-id
   :timestamp timestamp
   :content content
   :topic topic
   :stream stream
   :word-count (count (str/split content #"\\s+"))
   :length (count content)
   :has-code (str/includes? content "```")
   :has-latex (str/includes? content "\\\\")
   :has-link (str/includes? content "http")})

(defn extract-message-entities
  \"Extract named entities from message content
   Input: message record
   Output: entities map\"
  [message]

  (let [content (:content message)
        words (str/split (str/lower-case content) #"\\W+")

        ;; Heuristic: capitalized words might be entity names
        potential-entities (filter (fn [word]
                                   (and (> (count word) 3)
                                       (Character/isUpperCase (first word))))
                                 (str/split content #"\\s+"))

        ;; Mathematical concepts (heuristic keywords)
        math-keywords ["functor" "category" "morphism" "object" "algebra"
                      "topology" "homology" "cohomology" "sheaf" "topos"
                      "adjoint" "natural" "monad" "comonad"]

        found-math (filter (fn [keyword]
                           (some #(str/includes? (str/lower-case %) keyword)
                                words))
                         math-keywords)]

    {:potential-entities potential-entities
     :math-keywords found-math
     :entity-count (count potential-entities)
     :keyword-count (count found-math)}))

;; =============================================================================
;; Section 2: Temporal Window and Clustering
;; =============================================================================

(defn create-temporal-window
  \"Define time window for conversation clustering
   Input: window-size-minutes
   Output: window specification\"
  [window-minutes]

  {:window-size-ms (* window-minutes 60 1000)
   :window-minutes window-minutes
   :description (str "Temporal window: " window-minutes " minutes")})

(defn cluster-messages-by-time
  \"Group messages into temporal clusters (conversations)
   Input: sorted messages, temporal window
   Output: clusters with temporal bounds\"
  [messages temporal-window]

  (let [window-ms (:window-size-ms temporal-window)

        ;; Group messages that are close in time
        clusters (reduce (fn [acc message]
                         (let [last-cluster (peek acc)
                               last-ts (if last-cluster
                                       (apply max (map :timestamp last-cluster))
                                       0)
                               current-ts (:timestamp message)
                               gap (- current-ts last-ts)]

                           (if (and last-cluster (< gap window-ms))
                             ;; Add to existing cluster
                             (conj (pop acc) (conj last-cluster message))
                             ;; Start new cluster
                             (conj acc [message]))))
                        []
                        messages)]

    {:clusters clusters
     :total-clusters (count clusters)
     :window-minutes (:window-minutes temporal-window)
     :messages-per-cluster (map count clusters)}))

(defn summarize-cluster
  \"Create summary for a temporal cluster (conversation)
   Input: message cluster
   Output: cluster summary\"
  [cluster]

  (let [start-time (apply min (map :timestamp cluster))
        end-time (apply max (map :timestamp cluster))
        duration-minutes (/ (- end-time start-time) 60000.0)

        senders (set (map :sender-id cluster))
        topics (set (map :topic cluster))
        streams (set (map :stream cluster))

        total-words (reduce + (map :word-count cluster))
        total-length (reduce + (map :length cluster))

        code-messages (count (filter :has-code cluster))
        latex-messages (count (filter :has-latex cluster))
        link-messages (count (filter :has-link cluster))]

    {:cluster-start start-time
     :cluster-end end-time
     :duration-minutes duration-minutes
     :message-count (count cluster)
     :participant-count (count senders)
     :participants (vec senders)
     :topics (vec topics)
     :streams (vec streams)
     :total-words total-words
     :avg-words-per-message (/ total-words (count cluster))
     :code-blocks code-messages
     :latex-formulas latex-messages
     :links link-messages
     :content-type (cond
                    (> latex-messages 0) :mathematical
                    (> code-messages 0) :technical
                    (> link-messages 0) :referential
                    :else :conversational)}))

;; =============================================================================
;; Section 3: Interaction Sequences
;; =============================================================================

(defn extract-interaction-sequence
  \"Extract sequence of interactions between participants
   Input: cluster
   Output: interaction sequence\"
  [cluster]

  (let [;; Order messages by timestamp
        ordered (sort-by :timestamp cluster)

        ;; Track who spoke when
        interactions (reduce (fn [acc message]
                            (let [sender (:sender-id message)
                                  prev-sender (when-let [prev (last acc)]
                                             (:speaker prev))
                                  is-continuation (= sender prev-sender)]

                              (conj acc
                               {:speaker sender
                                :timestamp (:timestamp message)
                                :content-length (:length message)
                                :is-continuation is-continuation
                                :has-code (:has-code message)
                                :has-math (:has-math message)})))
                           []
                           ordered)]

    {:sequence interactions
     :length (count interactions)
     :unique-speakers (count (set (map :speaker interactions)))
     :longest-turn (apply max (map (fn [i]
                                   (count (take-while #(= (:speaker %) (:speaker i))
                                                     (drop-while #(not= (:speaker %) (:speaker i))
                                                                interactions))))
                                  (range (count interactions))))}))

(defn compute-interaction-patterns
  \"Analyze patterns in interaction sequences
   Input: interaction sequence
   Output: pattern statistics\"
  [interaction-seq]

  (let [sequence (:sequence interaction-seq)
        speakers (map :speaker sequence)

        ;; Speaker transitions
        transitions (vec (map vector
                            speakers
                            (rest speakers)))

        ;; Count unique speaker pairs
        pair-frequencies (frequencies transitions)
        most-common-pair (key (apply max-key val pair-frequencies))

        ;; Turn lengths
        turn-lengths (reduce (fn [acc speaker]
                            (let [turns (count (filter #(= speaker (:speaker %)) sequence))]
                              (conj acc turns)))
                           []
                           (set speakers))

        avg-turn-length (/ (reduce + turn-lengths) (count turn-lengths))]

    {:pair-frequencies pair-frequencies
     :most-common-pair most-common-pair
     :turn-length-avg avg-turn-length
     :turn-length-max (apply max turn-lengths)
     :turn-length-min (apply min turn-lengths)}))

;; =============================================================================
;; Section 4: Causal Relationship Discovery
;; =============================================================================

(defn detect-response-pairs
  \"Identify message response relationships (who replied to whom)
   Input: cluster of messages
   Output: response graph\"
  [cluster]

  (let [ordered (sort-by :timestamp cluster)

        ;; Simple heuristic: message B responds to message A if:
        ;; 1. B comes shortly after A (< 5 min window)
        ;; 2. Different sender than A
        response-window-ms (* 5 60 1000)

        responses (reduce (fn [acc i]
                         (let [current (nth ordered i)
                               previous-candidates (filter (fn [j]
                                                            (and (< j i)
                                                                (not= (:sender-id current)
                                                                     (:sender-id (nth ordered j)))
                                                                (< (- (:timestamp current)
                                                                     (:timestamp (nth ordered j)))
                                                                   response-window-ms)))
                                                          (range i))

                               likely-parent (when (seq previous-candidates)
                                            (nth ordered (last previous-candidates)))]

                           (if likely-parent
                             (conj acc {:response-to (:message-id likely-parent)
                                       :responder (:sender-id current)
                                       :respondee (:sender-id likely-parent)
                                       :delay-minutes (/ (- (:timestamp current)
                                                           (:timestamp likely-parent))
                                                        60000.0)})
                             acc)))
                        []
                        (range 1 (count ordered)))]

    {:responses responses
     :response-count (count responses)
     :responder-count (count (set (map :responder responses)))
     :respondee-count (count (set (map :respondee responses)))}))

;; =============================================================================
;; Section 5: Topic Evolution Analysis
;; =============================================================================

(defn analyze-topic-evolution
  \"Track how discussion topics evolve over time
   Input: cluster of messages
   Output: topic progression\"
  [cluster]

  (let [ordered (sort-by :timestamp cluster)
        topics (map :topic ordered)

        ;; Topic transitions
        topic-transitions (vec (map vector
                              topics
                              (rest topics)))

        ;; Count same-topic continuations
        same-topic (count (filter (fn [[t1 t2]] (= t1 t2)) topic-transitions))
        topic-changes (count (filter (fn [[t1 t2]] (not= t1 t2)) topic-transitions))

        ;; Unique topics
        unique-topics (vec (set topics))]

    {:topics topics
     :unique-topics (count unique-topics)
     :topic-list (vec unique-topics)
     :same-topic-messages same-topic
     :topic-changes topic-changes
     :topic-stability (if (zero? (+ same-topic topic-changes))
                       0.0
                       (/ same-topic (+ same-topic topic-changes)))}))

;; =============================================================================
;; Section 6: Temporal Statistics
;; =============================================================================

(defn compute-temporal-statistics
  \"Compute overall temporal statistics across clusters
   Input: list of cluster summaries
   Output: temporal statistics\"
  [cluster-summaries]

  (let [durations (map :duration-minutes cluster-summaries)
        word-counts (map :total-words cluster-summaries)
        message-counts (map :message-count cluster-summaries)
        participant-counts (map :participant-count cluster-summaries)

        avg-duration (/ (reduce + durations) (count durations))
        max-duration (apply max durations)
        min-duration (apply min durations)

        avg-words (/ (reduce + word-counts) (count word-counts))
        avg-messages (/ (reduce + message-counts) (count message-counts))
        avg-participants (/ (reduce + participant-counts) (count participant-counts))]

    {:cluster-count (count cluster-summaries)
     :avg-duration-minutes avg-duration
     :max-duration-minutes max-duration
     :min-duration-minutes min-duration
     :avg-words-per-cluster avg-words
     :avg-messages-per-cluster avg-messages
     :avg-participants-per-cluster avg-participants
     :total-messages (reduce + message-counts)
     :total-participants (count (set (mapcat :participants cluster-summaries)))}))

;; =============================================================================
;; Section 7: Pattern Frequency Analysis
;; =============================================================================

(defn analyze-pattern-frequency
  \"Analyze frequency of interaction patterns
   Input: list of interaction pattern analysis results
   Output: frequency statistics\"
  [pattern-analyses]

  (let [all-pairs (mapcat (fn [analysis]
                          (keys (:pair-frequencies analysis)))
                        pattern-analyses)

        pair-freq (frequencies all-pairs)
        most-common (apply max-key val pair-freq)

        content-types (mapcat (fn [summary]
                              [(:content-type summary)])
                            (map :cluster summary pattern-analyses))

        type-frequencies (frequencies content-types)]

    {:common-speaker-pairs (into {} (sort-by val > pair-freq))
     :most-common-pair (first most-common)
     :most-common-pair-freq (second most-common)
     :content-type-distribution type-frequencies
     :pattern-diversity (count pair-freq)}))

;; =============================================================================
;; Section 8: Temporal Pattern Export
;; =============================================================================

(defn export-temporal-patterns
  \"Export temporal patterns for downstream processing
   Input: all temporal analysis results
   Output: JSON-serializable structure\"
  [clusters interactions responses topics stats patterns]

  {:temporal-analysis
   {:cluster-count (:cluster-count stats)
    :total-messages (:total-messages stats)
    :total-participants (:total-participants stats)
    :avg-cluster-duration (:avg-duration-minutes stats)
    :avg-cluster-size (:avg-messages-per-cluster stats)}

   :interaction-patterns
   {:common-pairs (:common-speaker-pairs patterns)
    :content-type-dist (:content-type-distribution patterns)
    :pattern-diversity (:pattern-diversity patterns)}

   :response-analysis
   {:total-responses (:response-count (first responses))
    :responder-count (:responder-count (first responses))}

   :topic-evolution
   {:avg-stability (/ (reduce + (map :topic-stability topics))
                    (count topics))
    :avg-topic-changes (/ (reduce + (map :topic-changes topics))
                         (count topics))}})

;; =============================================================================
;; Section 9: Main Discovery Pipeline
;; =============================================================================

(defn discover-temporal-patterns
  \"Main pipeline for temporal pattern discovery
   Input: sorted message list, temporal window size
   Output: comprehensive temporal pattern analysis\"
  [messages window-minutes]

  (println \"\\n╔══════════════════════════════════════════════════════════╗\")
  (println \"║  PHASE 6: TEMPORAL PATTERN DISCOVERY                     ║\")
  (println \"╚══════════════════════════════════════════════════════════╝\\n\")

  (let [;; Create temporal window
        temporal-window (create-temporal-window window-minutes)

        ;; Cluster messages by time
        clustering (cluster-messages-by-time messages temporal-window)
        clusters (:clusters clustering)

        ;; Analyze each cluster
        cluster-summaries (map summarize-cluster clusters)
        interaction-seqs (map extract-interaction-sequence clusters)
        response-pairs (map detect-response-pairs clusters)
        topic-evolutions (map analyze-topic-evolution clusters)

        ;; Compute statistics
        temporal-stats (compute-temporal-statistics cluster-summaries)
        pattern-freqs (analyze-pattern-frequency
                      (map compute-interaction-patterns interaction-seqs))

        ;; Export results
        export (export-temporal-patterns
               clusters interaction-seqs response-pairs
               topic-evolutions temporal-stats pattern-freqs)]

    ;; Print summary
    (println \"📊 TEMPORAL CLUSTERING\")
    (println \"─────────────────────────────────────────────────────────\")
    (printf \"  Total messages: %d%n\" (:total-messages temporal-stats))
    (printf \"  Temporal clusters found: %d%n\" (:cluster-count temporal-stats))
    (printf \"  Unique participants: %d%n\" (:total-participants temporal-stats))
    (printf \"  Avg cluster duration: %.1f minutes%n\" (:avg-duration-minutes temporal-stats))
    (printf \"  Avg messages per cluster: %.1f%n\" (:avg-messages-per-cluster temporal-stats))

    (println \"\\n🔄 INTERACTION PATTERNS\")
    (println \"─────────────────────────────────────────────────────────\")
    (printf \"  Content types: %s%n\" (:content-type-distribution pattern-freqs))
    (printf \"  Unique speaker pair patterns: %d%n\" (:pattern-diversity pattern-freqs))

    (println \"\\n✅ TEMPORAL DISCOVERY COMPLETE\")

    {:cluster-summaries cluster-summaries
     :interaction-sequences interaction-seqs
     :response-analysis response-pairs
     :topic-evolution topic-evolutions
     :temporal-statistics temporal-stats
     :pattern-frequencies pattern-freqs
     :export export}))
