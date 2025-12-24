(ns music-topos.curriculum
  "Pure curriculum compiler - generates ScoreEvents without side effects.
   Compiles curriculum sections into sequences of ScoreEvents for playback."
  (:require [music-topos.score :as score]
            [music-topos.core :as core]))

;; ============================================================================
;; PURE EVENT GENERATORS
;; ============================================================================

(defn pitch-class-events
  "Generate events for a sequence of pitches.
   Returns seq of ScoreEvents starting at start-beat."
  [start-beat pitches dur gap]
  (map-indexed
   (fn [i pitch]
     (score/make-score-event
      {:id (keyword (str "pitch-" i))
       :at (+ start-beat (* i (+ dur gap)))
       :dur dur
       :world-object (score/make-world-object
                      {:type :pitch-space
                       :value {:midi pitch :index i}})
       :audio (score/audio-from-midi pitch :amplitude 0.2)}))
   pitches))

(defn harmonic-function-events
  "Generate events for harmonic functions (T, S, D, etc.).
   Each function contains a chord."
  [start-beat functions dur gap]
  (map-indexed
   (fn [i hf]
     (score/make-score-event
      {:id (keyword (str "harmonic-" (:name hf)))
       :at (+ start-beat (* i (+ dur gap)))
       :dur dur
       :world-object (score/make-world-object
                      {:type :harmonic-world
                       :value {:name (:name hf)
                               :root (:root hf)
                               :chord (:chord hf)}})
       :audio (score/audio-from-midi (:chord hf) :amplitude 0.2)}))
   functions))

(defn modulation-events
  "Generate events for modulation intervals (circle of fifths, etc.)."
  [start-beat intervals base-pitch dur gap]
  (map-indexed
   (fn [i interval]
     (let [pitch (+ base-pitch interval)]
       (score/make-score-event
        {:id (keyword (str "modulation-" i))
         :at (+ start-beat (* i (+ dur gap)))
         :dur dur
         :world-object (score/make-world-object
                        {:type :transformation-world
                         :value {:interval interval
                                 :pitch pitch
                                 :index i}
                         :morphisms [:transpose]})
         :audio (score/audio-from-midi pitch :amplitude 0.25)})))
   intervals))

(defn chord-progression-events
  "Generate events for a chord progression."
  [start-beat chords dur gap]
  (map-indexed
   (fn [i chord]
     (let [notes (if (map? chord) (:notes chord) chord)
           name (if (map? chord) (:name chord) (str "chord-" i))]
       (score/make-score-event
        {:id (keyword (str "chord-" i))
         :at (+ start-beat (* i (+ dur gap)))
         :dur dur
         :world-object (score/make-world-object
                        {:type :chord-space
                         :value {:name name :notes notes}})
         :audio (score/audio-from-midi notes :amplitude 0.2)})))
   chords))

(defn single-pitch-event
  "Generate a single pitch event."
  [id at dur pitch amplitude]
  (score/make-score-event
   {:id id
    :at at
    :dur dur
    :world-object (score/make-world-object
                   {:type :pitch-space
                    :value {:midi pitch}})
    :audio (score/audio-from-midi pitch :amplitude amplitude)}))

;; ============================================================================
;; INITIAL WORLD COMPILER
;; ============================================================================

(defn compile-initial-world
  "Compile the initial-world into a sequence of ScoreEvents.
   Returns pure data - a vector of ScoreEvents.
   
   Structure:
   - Section 1: Initial pitch C4 at beat 0
   - Section 2: Pitch classes at beat 3  
   - Section 3: Harmonic functions at beat 5
   - Section 4: Modulation (circle of fifths) at beat 10"
  [tempo]
  (let [world core/initial-world]
    (vec
     (concat
      ;; Section 1: Initial pitch (C4)
      [(single-pitch-event :initial-pitch 0 2.0 60 0.3)]
      
      ;; Section 2: All 12 pitch classes
      (pitch-class-events 3 (:pitch-classes world) 0.1 0.05)
      
      ;; Section 3: Harmonic functions (T→S→D→T)
      (harmonic-function-events 5 (:harmonic-functions world) 0.8 0.4)
      
      ;; Section 4: Modulation (circle of fifths)
      (modulation-events 10 (:modulation-keys world) 60 0.5 0.2)))))

;; ============================================================================
;; TERMINAL WORLD COMPILER (Sonata Form)
;; ============================================================================

(defn compile-terminal-world
  "Compile the terminal-world (sonata form) into ScoreEvents.
   
   Structure:
   - Exposition: Theme 1 and Theme 2
   - Development: Key exploration
   - Recapitulation: Theme 1 return
   - Coda: Cadence and final chord"
  [tempo]
  (let [world core/terminal-world
        structure (:structure world)
        exposition (:exposition structure)
        development (:development structure)
        coda (:coda structure)]
    (vec
     (concat
      ;; EXPOSITION: Theme 1 at beat 0, Theme 2 at beat 2
      [(score/make-score-event
        {:id :exposition-theme-1
         :at 0
         :dur 0.8
         :world-object (score/make-world-object
                        {:type :chord-space
                         :value {:section :exposition
                                 :theme 1
                                 :notes (first (:themes exposition))}})
         :audio (score/audio-from-midi (first (:themes exposition)) :amplitude 0.2)})
       
       (score/make-score-event
        {:id :exposition-theme-2
         :at 2
         :dur 0.8
         :world-object (score/make-world-object
                        {:type :chord-space
                         :value {:section :exposition
                                 :theme 2
                                 :notes (second (:themes exposition))}})
         :audio (score/audio-from-midi (second (:themes exposition)) :amplitude 0.2)})]
      
      ;; DEVELOPMENT: Key exploration starting at beat 4
      (map-indexed
       (fn [i pitch]
         (score/make-score-event
          {:id (keyword (str "development-" i))
           :at (+ 4 (* i 0.6))
           :dur 0.4
           :world-object (score/make-world-object
                          {:type :pitch-space
                           :value {:section :development
                                   :exploration true
                                   :midi pitch}})
           :audio (score/audio-from-midi pitch :amplitude 0.2)}))
       (:keys development))
      
      ;; RECAPITULATION: Theme 1 return at beat 8
      [(score/make-score-event
        {:id :recapitulation-theme-1
         :at 8
         :dur 0.8
         :world-object (score/make-world-object
                        {:type :chord-space
                         :value {:section :recapitulation
                                 :return true
                                 :notes (first (:themes exposition))}})
         :audio (score/audio-from-midi (first (:themes exposition)) :amplitude 0.2)})]
      
      ;; CODA: Cadence notes at beat 10, final chord at beat 11
      (map-indexed
       (fn [i note]
         (score/make-score-event
          {:id (keyword (str "coda-cadence-" i))
           :at (+ 10 (* i 0.5))
           :dur 0.4
           :world-object (score/make-world-object
                          {:type :pitch-space
                           :value {:section :coda
                                   :cadence true
                                   :midi note}})
           :audio (score/audio-from-midi note :amplitude 0.3)}))
       (:cadence coda))
      
      ;; Final chord
      [(score/make-score-event
        {:id :coda-final
         :at 12
         :dur 2.0
         :world-object (score/make-world-object
                        {:type :chord-space
                         :value {:section :coda
                                 :final true
                                 :notes (first (:themes exposition))}})
         :audio (score/audio-from-midi (first (:themes exposition)) :amplitude 0.3)})]))))

;; ============================================================================
;; FULL CURRICULUM COMPILER
;; ============================================================================

(defn compile-full-curriculum
  "Compile all curriculum worlds into a single score.
   Returns {:tempo tempo :events [...]} with all ScoreEvents."
  ([]
   (compile-full-curriculum 120))
  ([tempo]
   (let [initial-events (compile-initial-world tempo)
         ;; Terminal world starts after initial world ends
         ;; Calculate offset based on last event in initial world
         initial-end (if (seq initial-events)
                       (let [last-evt (last initial-events)]
                         (+ (:at last-evt) (:dur last-evt)))
                       0)
         terminal-offset (+ initial-end 2) ;; 2 beat gap
         terminal-events (compile-terminal-world tempo)
         ;; Offset terminal events
         offset-terminal (mapv
                          (fn [evt]
                            (assoc evt :at (+ (:at evt) terminal-offset)))
                          terminal-events)]
     {:tempo tempo
      :worlds [{:name "initial-world"
                :start-beat 0
                :events initial-events}
               {:name "terminal-world"
                :start-beat terminal-offset
                :events offset-terminal}]
      :events (vec (concat initial-events offset-terminal))})))

;; ============================================================================
;; UTILITY FUNCTIONS
;; ============================================================================

(defn score-duration
  "Calculate total duration of a score in beats."
  [score]
  (if-let [events (seq (:events score))]
    (let [last-evt (apply max-key #(+ (:at %) (:dur %)) events)]
      (+ (:at last-evt) (:dur last-evt)))
    0))

(defn score-duration-seconds
  "Calculate total duration of a score in seconds."
  [score]
  (score/beats->seconds (:tempo score) (score-duration score)))

(defn events-at-beat
  "Get all events that are sounding at a given beat."
  [events beat]
  (filter
   (fn [evt]
     (and (<= (:at evt) beat)
          (> (+ (:at evt) (:dur evt)) beat)))
   events))

(comment
  ;; Development/testing
  (def test-score (compile-full-curriculum 120))
  (count (:events test-score))
  (score-duration test-score)
  (score-duration-seconds test-score)
  
  ;; Inspect initial world events
  (compile-initial-world 120)
  
  ;; Inspect terminal world events  
  (compile-terminal-world 120))
