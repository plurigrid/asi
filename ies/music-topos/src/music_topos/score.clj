(ns music-topos.score
  "Shared ScoreEvent abstraction for music-topos curriculum.
   Matches lib/score_event.rb for cross-language compatibility.")

;;; Helper functions

(defn midi->hz
  "Convert MIDI note number to frequency in Hz."
  [midi-note]
  (* 440.0 (Math/pow 2.0 (/ (- midi-note 69) 12.0))))

(defn beats->seconds
  "Convert beats to seconds at given tempo (BPM)."
  [tempo beats]
  (* (/ 60.0 tempo) beats))

;;; World object types (categorical/topological spaces)

(def world-object-types
  #{:pitch-space
    :chord-space
    :harmonic-world
    :transformation-world})

;;; Audio parameters

(defrecord Audio [frequencies amplitude synth])

(defn make-audio
  "Create Audio from frequencies (Hz), amplitude, and synth name."
  [{:keys [frequencies amplitude synth]
    :or {amplitude 0.3 synth :default}}]
  (->Audio (vec frequencies) amplitude synth))

(defn audio-from-midi
  "Create Audio from MIDI note numbers."
  [midi-notes & {:keys [amplitude synth] :or {amplitude 0.3 synth :default}}]
  (make-audio {:frequencies (mapv midi->hz (if (sequential? midi-notes)
                                             midi-notes
                                             [midi-notes]))
               :amplitude amplitude
               :synth synth}))

;;; World objects

(defrecord WorldObject [type value morphisms])

(defn make-world-object
  "Create a WorldObject with type validation."
  [{:keys [type value morphisms] :or {morphisms []}}]
  (when-not (world-object-types type)
    (throw (ex-info (str "Unknown world type: " type)
                    {:type type :valid-types world-object-types})))
  (->WorldObject type value morphisms))

;;; Score events

(defrecord ScoreEvent [id at dur world-object audio meta])

(defn make-score-event
  "Create a ScoreEvent.
   - id: unique identifier
   - at: start time in beats
   - dur: duration in beats
   - world-object: categorical/topological structure
   - audio: Audio record with frequencies, amplitude, synth
   - meta: optional metadata map"
  [{:keys [id at dur world-object audio meta]}]
  (->ScoreEvent id at dur world-object audio (or meta {})))

(defn event-at-seconds
  "Get event start time in seconds."
  [event tempo]
  (beats->seconds tempo (:at event)))

(defn event-dur-seconds
  "Get event duration in seconds."
  [event tempo]
  (beats->seconds tempo (:dur event)))

(defn event->osc-bundle
  "Convert ScoreEvent to OSC-friendly map."
  [event tempo]
  (let [audio (:audio event)]
    {:time (event-at-seconds event tempo)
     :duration (event-dur-seconds event tempo)
     :frequencies (or (:frequencies audio) [])
     :amplitude (or (:amplitude audio) 0.3)
     :synth (or (:synth audio) :default)}))

(defn event->map
  "Convert ScoreEvent to plain map for serialization."
  [event]
  {:id (:id event)
   :at (:at event)
   :dur (:dur event)
   :world-object (when-let [wo (:world-object event)]
                   {:type (:type wo)
                    :value (:value wo)
                    :morphisms (:morphisms wo)})
   :audio (when-let [a (:audio event)]
            {:frequencies (:frequencies a)
             :amplitude (:amplitude a)
             :synth (:synth a)})
   :meta (:meta event)})
