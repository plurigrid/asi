(ns agents.colorable-music-topos
  "Colorable Music Topos: Color-Sound-Topology Synthesis

  Maps interactions to colors (via optimal Gay seed),
  then to musical/sonic properties in real-time.

  Status: 2025-12-21 - Live colorable synesthetic system"
  (:require [clojure.string :as str]
            [agents.optimal-seed-selection :as seed]
            [agents.leitmotif-recognition :as leitmotif]
            [agents.entropy-metrics :as entropy]))

;; =============================================================================
;; Section 1: Color to Musical Mapping
;; =============================================================================

(defn hue-to-midi-pitch
  "Map hue (0-360) to MIDI pitch (12-127)"
  [hue]
  (let [normalized (/ hue 360)
        octaves 8  ; Span 8 octaves
        midi-base 24  ; C1
        semitones (* normalized 12 octaves)]
    (int (+ midi-base semitones))))

(defn saturation-to-velocity
  "Map saturation (0-1) to MIDI velocity (0-127)"
  [saturation]
  (int (* saturation 127)))

(defn lightness-to-duration
  "Map lightness (0-1) to note duration in ms"
  [lightness]
  (let [base-duration 250  ; 250ms base
        max-duration 4000  ; 4 seconds max
        factor (+ 1 (* lightness 3))]  ; 1x to 4x
    (int (* base-duration factor))))

(defn color-to-note
  "Convert color (HSV) to musical note"
  [color]
  (let [{:keys [hue saturation value]} color]
    {:pitch (hue-to-midi-pitch hue)
     :velocity (saturation-to-velocity saturation)
     :duration (lightness-to-duration value)
     :color color}))

;; =============================================================================
;; Section 2: Leitmotif to Timbre
;; =============================================================================

(def leitmotif-timbres
  "Timbre/synthesis parameters for each leitmotif"
  {:technical-innovation
   {:synth :sine
    :filter {:type :lowpass :freq 3000}
    :envelope {:attack 50 :decay 100 :sustain 0.7 :release 200}}

   :collaborative-work
   {:synth :triangle
    :filter {:type :bandpass :freq 1500}
    :envelope {:attack 100 :decay 150 :sustain 0.6 :release 300}}

   :philosophical-reflection
   {:synth :saw
    :filter {:type :highpass :freq 800}
    :envelope {:attack 200 :decay 100 :sustain 0.8 :release 400}}

   :network-building
   {:synth :pulse
    :filter {:type :lowpass :freq 2000}
    :envelope {:attack 30 :decay 80 :sustain 0.9 :release 150}}

   :musical-creation
   {:synth :sine
    :filter {:type :allpass :freq 2500}
    :envelope {:attack 150 :decay 200 :sustain 0.5 :release 300}}

   :synthesis
   {:synth :square
    :filter {:type :bandpass :freq 2000}
    :envelope {:attack 75 :decay 125 :sustain 0.7 :release 250}}})

(defn leitmotif-to-timbre
  "Get timbre parameters for a leitmotif"
  [leitmotif-name]
  (get leitmotif-timbres leitmotif-name
       {:synth :sine
        :filter {:type :lowpass :freq 2000}
        :envelope {:attack 100 :decay 100 :sustain 0.7 :release 200}}))

;; =============================================================================
;; Section 3: Entropy to Dynamics
;; =============================================================================

(defn entropy-to-dynamics
  "Map entropy level to dynamics (loudness variation)"
  [entropy]
  (let [normalized (/ entropy 4.0)  ; Normalize to 0-1
        dynamics (cond
                  (< normalized 0.3) :ppp  ; Soft
                  (< normalized 0.5) :pp
                  (< normalized 0.7) :p
                  (< normalized 0.85) :mf  ; Medium
                  (< normalized 0.95) :f
                  :else :ff)]  ; Loud
    dynamics))

(defn entropy-to-tempo
  "Map entropy to tempo (BPM)"
  [entropy]
  (let [normalized (/ entropy 4.0)
        base-tempo 60
        max-tempo 180
        tempo (int (+ base-tempo (* normalized (- max-tempo base-tempo))))]
    tempo))

;; =============================================================================
;; Section 4: Interaction to Colorable Musical Event
;; =============================================================================

(defn interaction-to-musical-event
  "Convert interaction → color → musical event"
  [interaction optimal-seed tagged-interaction]
  (let [{:keys [primary-leitmotif color]} tagged-interaction

        ;; Map color to note
        note (color-to-note color)

        ;; Get timbre from leitmotif
        timbre (leitmotif-to-timbre primary-leitmotif)

        ;; Create event
        event {:interaction-id (:id interaction)
               :timestamp (:timestamp interaction)
               :leitmotif primary-leitmotif
               :color color
               :note note
               :timbre timbre
               :synth (:synth timbre)
               :pitch (:pitch note)
               :velocity (:velocity note)
               :duration (:duration note)
               :filter (:filter timbre)
               :envelope (:envelope timbre)}]

    event))

;; =============================================================================
;; Section 5: Event Stream to Musical Sequence
;; =============================================================================

(defn interactions-to-musical-sequence
  "Convert interaction stream to playable musical sequence"
  [interactions optimal-seed tagged-interactions]
  (mapv (fn [i tagged]
          (interaction-to-musical-event i optimal-seed tagged))
        interactions
        tagged-interactions))

(defn sequence-to-timeline
  "Arrange events on a timeline with proper timing"
  [musical-sequence]
  (let [sorted (sort-by :timestamp musical-sequence)
        first-time (:timestamp (first sorted))

        with-offsets
        (map (fn [event]
               (let [offset (- (:timestamp event) first-time)
                     offset-seconds (/ offset 1000)]
                 (assoc event :offset-seconds offset-seconds)))
             sorted)]

    with-offsets))

;; =============================================================================
;; Section 6: Visual Representation
;; =============================================================================

(defn color-to-ansi-hex
  "Convert color to ANSI hex for terminal display"
  [color]
  (let [{:keys [hue saturation value]} color
        ;; Simple HSV to RGB conversion
        h-segment (/ hue 60)
        c (* saturation value)
        h-mod (mod h-segment 2)
        x (* c (- 1 (Math/abs (- h-mod 1))))

        [r' g' b'] (cond
                     (< h-segment 1) [c x 0]
                     (< h-segment 2) [x c 0]
                     (< h-segment 3) [0 c x]
                     (< h-segment 4) [0 x c]
                     (< h-segment 5) [x 0 c]
                     :else [c 0 x])

        m (- value c)
        r (int (* 255 (+ r' m)))
        g (int (* 255 (+ g' m)))
        b (int (* 255 (+ b' m)))]

    (format "%02x%02x%02x" r g b)))

(defn display-musical-event
  "Display a musical event with color"
  [event]
  (let [color-hex (color-to-ansi-hex (:color event))
        leitmotif (:leitmotif event)
        pitch-name (midi-to-note (:pitch event))]

    (println (str
             "█ [" (format "%10.2f" (:offset-seconds event)) "s] "
             "Pitch: " (format "%3d" (:pitch event)) " "
             "(" pitch-name ") "
             "Vel: " (format "%3d" (:velocity event)) " "
             "Dur: " (format "%4d" (:duration event)) "ms "
             "Leitmotif: " (str/replace (str leitmotif) #":" "")))))

(defn display-colorable-sequence
  "Display entire musical sequence with colors"
  [musical-timeline]
  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║          COLORABLE MUSIC TOPOS - EVENT TIMELINE          ║")
  (println "╚══════════════════════════════════════════════════════════╝\n")

  (doseq [event musical-timeline]
    (display-musical-event event))

  (println "\n" (count musical-timeline) "events generated"))

;; =============================================================================
;; Section 7: OSC/SuperCollider Integration
;; =============================================================================

(defn event-to-osc-message
  "Convert musical event to OSC message for SuperCollider"
  [event]
  {:synth (:synth event)
   :args [:pitch (:pitch event)
          :velocity (:velocity event)
          :duration (:duration event)
          :attack (get-in event [:envelope :attack])
          :decay (get-in event [:envelope :decay])
          :sustain (get-in event [:envelope :sustain])
          :release (get-in event [:envelope :release])
          :filter-type (get-in event [:filter :type])
          :filter-freq (get-in event [:filter :freq])]})

(defn generate-supercollider-code
  "Generate SuperCollider code to play the sequence"
  [musical-timeline]
  (let [osc-messages (map event-to-osc-message musical-timeline)
        sc-lines (map (fn [msg offset]
                       (str "(" offset ").wait; "
                            "Synth(\\\"" (:synth msg) "\\\", ["
                            (str/join ", " (partition 2 (:args msg)))
                            "]);"))
                     osc-messages
                     (map :offset-seconds musical-timeline))]

    (str/join "\n" sc-lines)))

;; =============================================================================
;; Section 8: Complete Pipeline
;; =============================================================================

(defn colorable-music-topos-pipeline
  "Complete pipeline: interactions → colors → music → sound"
  [interactions interaction-entropy-baseline]
  (let [;; Step 1: Select optimal seed from entropy
        seed-result (seed/select-optimal-initial-seed interaction-entropy-baseline)
        optimal-seed (:optimal-seed seed-result)

        ;; Step 2: Tag interactions with leitmotifs & colors
        tagged (leitmotif/tag-interactions-with-leitmotifs
               interactions optimal-seed)

        ;; Step 3: Convert to musical events
        musical-events (interactions-to-musical-sequence
                       interactions optimal-seed tagged)

        ;; Step 4: Arrange on timeline
        timeline (sequence-to-timeline musical-events)

        ;; Step 5: Generate visualization & code
        sc-code (generate-supercollider-code timeline)]

    {:optimal-seed optimal-seed
     :seed-entropy (:entropy seed-result)
     :target-entropy (:target-entropy seed-result)
     :tagged-interactions tagged
     :musical-events musical-events
     :timeline timeline
     :supercollider-code sc-code
     :num-events (count musical-events)
     :duration-seconds (apply max (map :offset-seconds timeline))}))

;; =============================================================================
;; Section 9: Display Summary
;; =============================================================================

(defn display-colorable-summary
  "Display complete colorable music topos summary"
  [result]
  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║       COLORABLE MUSIC TOPOS - COMPLETE PIPELINE         ║")
  (println "╚══════════════════════════════════════════════════════════╝\n")

  (println "OPTIMAL SEED SELECTION:")
  (println (str "  Optimal Seed: " (:optimal-seed result)))
  (println (str "  Seed Entropy: " (format "%.2f" (:seed-entropy result)) " bits"))
  (println (str "  Target Entropy: " (format "%.2f" (:target-entropy result)) " bits"))
  (println "")

  (println "MUSICAL COMPOSITION:")
  (println (str "  Total Events: " (:num-events result)))
  (println (str "  Duration: " (format "%.1f" (:duration-seconds result)) " seconds"))
  (println "")

  (println "VISUALIZATION:")
  (display-colorable-sequence (:timeline result))
  (println "")

  (println "SUPERCOLLIDER CODE (first 5 lines):")
  (let [lines (str/split (:supercollider-code result) #"\n")
        first-5 (take 5 lines)]
    (doseq [line first-5]
      (println "  " line)))
  (if (> (count (str/split (:supercollider-code result) #"\n")) 5)
    (println "  ... (" (- (count (str/split (:supercollider-code result) #"\n")) 5) " more lines)"))
  (println ""))

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn midi-to-note
  "Convert MIDI pitch number to note name"
  [midi]
  (let [note-names ["C" "C#" "D" "D#" "E" "F" "F#" "G" "G#" "A" "A#" "B"]
        octave (quot (- midi 12) 12)
        pitch-class (mod midi 12)]
    (str (get note-names pitch-class) octave)))

;; =============================================================================
;; End of module
;; =============================================================================
