(ns agents.leitmotif-recognition
  "Leitmotif Recognition: Extract recurring semantic patterns

  Maps interaction patterns to recurring themes (leitmotifs):
  - Technical-innovation: Code, algorithms, system design
  - Collaborative-work: Team projects, joint creation
  - Philosophical-reflection: Deep thinking, meaning-making
  - Network-building: Connections, relationships, collaboration
  - Musical-creation: Sound, synthesis, rhythm
  - Synthesis: Integration of multiple domains

  Each leitmotif encodes to a hue range for color mapping.

  Status: 2025-12-21 - Ready for Phase 2 integration"
  (:require [clojure.string :as str]
            [clojure.math :as math]))

;; =============================================================================
;; Section 1: Leitmotif Definitions
;; =============================================================================

(def leitmotif-definitions
  "Complete leitmotif specification with hue mappings, keywords, and characteristics"
  {:technical-innovation
   {:description "Technical thinking, code, algorithms, system design"
    :hue-range [0 60]                    ; Red-Yellow zone
    :keywords ["code" "algorithm" "system" "design" "technical" "implement"
               "optimize" "data" "structure" "function" "api" "protocol"]
    :color-exemplar {:hue 30 :saturation 0.85 :value 0.95}
    :weight 1.0}

   :collaborative-work
   {:description "Team projects, joint work, co-creation"
    :hue-range [60 120]                  ; Yellow-Green zone
    :keywords ["team" "collaborate" "partner" "project" "work" "together"
               "contribute" "group" "collective" "share" "joint"]
    :color-exemplar {:hue 90 :saturation 0.8 :value 0.9}
    :weight 0.95}

   :philosophical-reflection
   {:description "Deep thinking, meaning, consciousness, being"
    :hue-range [120 180]                 ; Green-Cyan zone
    :keywords ["meaning" "consciousness" "identity" "perception" "being"
               "understand" "reflect" "think" "question" "explore" "contemplate"]
    :color-exemplar {:hue 150 :saturation 0.75 :value 0.88}
    :weight 1.0}

   :network-building
   {:description "Relationships, connections, graph theory, protocols"
    :hue-range [180 240]                 ; Cyan-Blue zone
    :keywords ["network" "connection" "relationship" "graph" "node" "edge"
               "protocol" "distribute" "peer" "link" "topology"]
    :color-exemplar {:hue 210 :saturation 0.8 :value 0.92}
    :weight 0.9}

   :musical-creation
   {:description "Sound, music, synthesis, rhythm, harmony"
    :hue-range [240 300]                 ; Blue-Purple zone
    :keywords ["music" "sound" "synthesis" "rhythm" "harmony" "beat"
               "overtone" "frequency" "oscillator" "wave" "tone"]
    :color-exemplar {:hue 270 :saturation 0.85 :value 0.90}
    :weight 1.0}

   :synthesis
   {:description "Integration of multiple domains, cross-domain thinking"
    :hue-range [300 360]                 ; Purple-Red zone
    :keywords ["integrate" "synthesis" "combine" "bridge" "connect" "cross"
               "meta" "framework" "system" "whole" "unified"]
    :color-exemplar {:hue 330 :saturation 0.8 :value 0.93}
    :weight 1.0}})

;; =============================================================================
;; Section 2: Feature Extraction
;; =============================================================================

(defn extract-text-features
  "Extract linguistic features from interaction content"
  [content]
  (let [words (str/lower-case (str content))
        word-count (count (str/split words #"\s+"))

        ;; Keyword presence scores
        has-tech (if (re-seq #"(code|algorithm|system|api|function)" words) 1 0)
        has-collab (if (re-seq #"(team|collaborate|partner|project|together)" words) 1 0)
        has-philo (if (re-seq #"(meaning|consciousness|identity|perception)" words) 1 0)
        has-network (if (re-seq #"(network|connection|graph|topology|protocol)" words) 1 0)
        has-music (if (re-seq #"(music|sound|synthesis|rhythm|harmony|tone)" words) 1 0)
        has-synthesis (if (re-seq #"(integrate|synthesis|combine|bridge|framework)" words) 1 0)

        ;; Formality (based on punctuation and length)
        question-marks (count (re-seq #"\?" words))
        exclamations (count (re-seq #"!" words))
        citations (count (re-seq #"[@#]" words))
        formality (/ (+ question-marks citations) (max 1 word-count))

        ;; Abstract vs concrete (heuristic)
        abstract-words (count (re-seq #"(concept|idea|theory|abstract|principle)" words))
        concrete-words (count (re-seq #"(implement|build|create|tool|artifact)" words))]

    {:word-count word-count
     :keyword-scores {:tech has-tech
                     :collab has-collab
                     :philo has-philo
                     :network has-network
                     :music has-music
                     :synthesis has-synthesis}
     :formality formality
     :abstract-level (if (zero? (+ abstract-words concrete-words))
                      0.5
                      (/ abstract-words (+ abstract-words concrete-words)))
     :citation-density citations}))

(defn extract-structural-features
  "Extract structural features from interaction metadata"
  [interaction]
  (let [has-reply (some? (:in-reply-to interaction))
        has-mentions (some? (:mentions interaction))
        has-links (some? (:links interaction))
        mentions-count (or (:mentions-count interaction) 0)
        links-count (or (:links-count interaction) 0)
        is-thread (some? (:thread-continuation interaction))
        collaborators-count (or (:collaborators-count interaction) 0)]

    {:is-reply has-reply
     :has-mentions has-mentions
     :has-links has-links
     :mentions-count mentions-count
     :links-count links-count
     :is-thread is-thread
     :collaborators-count collaborators-count
     :connectivity-score (+ mentions-count links-count collaborators-count)}))

;; =============================================================================
;; Section 3: Leitmotif Classification
;; =============================================================================

(defn score-leitmotif-match
  "Score how well an interaction matches each leitmotif (0-1)"
  [text-features structural-features]
  (let [keyword-scores (:keyword-scores text-features)

        ;; Weight keyword matches
        tech-score (* 0.4 (:tech keyword-scores))
        collab-score (* 0.4 (:collab keyword-scores)
                       (min 1.0 (/ (:connectivity-score structural-features) 5)))
        philo-score (* 0.5 (:philo keyword-scores)
                     (min 1.0 (:abstract-level text-features)))
        network-score (* 0.4 (:network keyword-scores)
                       (min 1.0 (/ (:connectivity-score structural-features) 3)))
        music-score (* 0.5 (:music keyword-scores))
        synthesis-score (* 0.3 (:synthesis keyword-scores)
                         (/ (+ (:tech keyword-scores) (:collab keyword-scores)
                               (:philo keyword-scores) (:network keyword-scores)
                               (:music keyword-scores)) 5))]

    {:technical-innovation (min 1.0 tech-score)
     :collaborative-work (min 1.0 collab-score)
     :philosophical-reflection (min 1.0 philo-score)
     :network-building (min 1.0 network-score)
     :musical-creation (min 1.0 music-score)
     :synthesis (min 1.0 synthesis-score)}))

(defn classify-primary-leitmotif
  "Determine primary leitmotif for an interaction (highest score wins)"
  [leitmotif-scores]
  (let [sorted (sort-by val > leitmotif-scores)
        primary (first sorted)
        top-score (val primary)]

    {:primary-leitmotif (key primary)
     :primary-score top-score
     :all-scores leitmotif-scores
     :confidence (if (> top-score 0.6) :high (if (> top-score 0.3) :medium :low))}))

;; =============================================================================
;; Section 4: Hue Mapping
;; =============================================================================

(defn leitmotif-to-hue
  "Map leitmotif to representative hue (0-360)"
  [leitmotif-name]
  (let [def (get leitmotif-definitions leitmotif-name)
        [hue-min hue-max] (:hue-range def)
        mid-point (/ (+ hue-min hue-max) 2)]
    mid-point))

(defn score-to-saturation
  "Convert leitmotif confidence score to saturation (0-1)"
  [score]
  (let [normalized (min 1.0 (max 0.0 score))]
    (+ 0.6 (* 0.35 normalized))))  ; Range: 0.6-0.95

(defn leitmotif-score-to-color
  "Convert leitmotif classification to color (HSV)"
  [leitmotif-name score]
  (let [hue (leitmotif-to-hue leitmotif-name)
        saturation (score-to-saturation score)
        value 0.90]  ; Consistent brightness

    {:hue hue
     :saturation saturation
     :value value
     :leitmotif leitmotif-name
     :score score}))

;; =============================================================================
;; Section 5: Batch Tagging Operations
;; =============================================================================

(defn tag-interaction-with-leitmotif
  "Complete pipeline: interaction → leitmotif classification → color"
  [interaction]
  (let [content (str (:content interaction) " " (:title interaction))
        text-features (extract-text-features content)
        struct-features (extract-structural-features interaction)

        leitmotif-scores (score-leitmotif-match text-features struct-features)
        classification (classify-primary-leitmotif leitmotif-scores)

        primary-leitmotif (:primary-leitmotif classification)
        primary-score (:primary-score classification)

        color (leitmotif-score-to-color primary-leitmotif primary-score)]

    (assoc interaction
           :leitmotif classification
           :primary-leitmotif primary-leitmotif
           :color color
           :leitmotif-scores (:all-scores classification))))

(defn tag-interactions-with-leitmotifs
  "Tag entire interaction sequence with leitmotifs and colors"
  [interactions]
  (mapv tag-interaction-with-leitmotif interactions))

(defn batch-tag-with-seed-offset
  "Tag interactions and optionally modulate colors based on seed
   (For optimal-seed integration in Phase 2)"
  [interactions seed]
  (let [tagged (tag-interactions-with-leitmotifs interactions)

        ;; Optional: Modulate saturation/value based on seed
        seed-normalized (/ (mod seed 360) 360)
        saturation-factor (+ 0.95 (* 0.05 seed-normalized))]

    (mapv (fn [interaction]
            (update-in interaction [:color :saturation]
                      #(min 1.0 (* % saturation-factor))))
          tagged)))

;; =============================================================================
;; Section 6: Verification and Display
;; =============================================================================

(defn leitmotif-distribution
  "Calculate distribution of leitmotifs in a sequence"
  [tagged-interactions]
  (let [leitmotifs (map :primary-leitmotif tagged-interactions)
        counts (frequencies leitmotifs)
        total (count leitmotifs)]

    (into {}
          (map (fn [[lm count]]
                 [lm {:count count
                      :proportion (double (/ count total))}])
               counts))))

(defn validate-leitmotif-tagging
  "Verify tagging quality and completeness"
  [tagged-interactions]
  (let [total (count tagged-interactions)
        with-leitmotif (count (filter :primary-leitmotif tagged-interactions))
        with-color (count (filter :color tagged-interactions))

        confidence-distribution (frequencies
                                (map #(get-in % [:leitmotif :confidence])
                                     tagged-interactions))

        avg-primary-score (double
                          (/ (reduce + (map #(get-in % [:leitmotif :primary-score]) tagged-interactions))
                             total))]

    {:total-tagged total
     :with-leitmotif with-leitmotif
     :with-color with-color
     :completeness (double (/ (+ with-leitmotif with-color) (* 2 total)))
     :confidence-distribution confidence-distribution
     :avg-primary-score avg-primary-score
     :quality (cond
               (>= avg-primary-score 0.7) :excellent
               (>= avg-primary-score 0.5) :good
               (>= avg-primary-score 0.3) :fair
               :else :poor)}))

(defn display-leitmotif-report
  "Display formatted leitmotif tagging report"
  [tagged-interactions]
  (let [distribution (leitmotif-distribution tagged-interactions)
        validation (validate-leitmotif-tagging tagged-interactions)]

    (println "\\n╔══════════════════════════════════════════════════════════╗")
    (println "║         LEITMOTIF RECOGNITION REPORT                      ║")
    (println "╚══════════════════════════════════════════════════════════╝\\n")

    (println "TAGGING COMPLETENESS:")
    (println (str "  Total interactions: " (:total-tagged validation)))
    (println (str "  Tagged with leitmotif: " (:with-leitmotif validation)))
    (println (str "  Tagged with color: " (:with-color validation)))
    (println (str "  Overall completeness: " (format \"%.1f%%\" (* 100 (:completeness validation)))))
    (println "")

    (println "QUALITY METRICS:")
    (println (str "  Average primary score: " (format \"%.2f\" (:avg-primary-score validation))))
    (println (str "  Quality rating: \" (str/upper-case (str (:quality validation)))))
    (println (str "  Confidence distribution: \" (pr-str (:confidence-distribution validation))))
    (println "")

    (println "LEITMOTIF DISTRIBUTION:")
    (doseq [[leitmotif info] (sort-by #(% :proportion) > distribution)]
      (let [bar-length (int (* 30 (:proportion info)))
            bar (str/join (repeat bar-length \"█\"))]
        (printf "  %25s: %3d (%5.1f%%) %s\\n"
               (str/replace (str leitmotif) #\":\" \"\")
               (:count info)
               (* 100 (:proportion info))
               bar)))
    (println "")))

(defn display-sample-leitmotif-tags
  "Display sample of tagged interactions with leitmotifs and colors"
  [tagged-interactions sample-size]
  (let [sample (take sample-size tagged-interactions)]

    (println "\\nSAMPLE TAGGED INTERACTIONS:")
    (println "───────────────────────────────────────────────────────\\n")

    (doseq [idx (range (count sample))
            :let [interaction (nth sample idx)
                  leitmotif (:primary-leitmotif interaction)
                  score (get-in interaction [:leitmotif :primary-score])
                  color (:color interaction)]]
      (printf "%2d. Leitmotif: %-25s Score: %.2f  Hue: %3d°\\n"
             (inc idx)
             (str/replace (str leitmotif) #\":\" \"\")
             score
             (int (:hue color))))))

;; =============================================================================
;; End of module
;; =============================================================================
