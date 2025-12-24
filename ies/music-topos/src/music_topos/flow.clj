(ns music-topos.flow
  "core.async flow-based pipeline for music curriculum.
   Provides composable, backpressure-aware event streaming."
  (:require [clojure.core.async :as a :refer [go go-loop <! >! >!! <!! 
                                               chan close! timeout 
                                               pipe mult tap onto-chan!
                                               sliding-buffer]]
            [music-topos.score :as score]
            [music-topos.curriculum :as curriculum]
            [music-topos.core :as core]
            [overtone.osc :as osc]))

;; ============================================================================
;; OSC CONNECTION (shared state for flow playback)
;; ============================================================================

(defonce ^:private flow-client (atom nil))

(defn flow-connect!
  "Connect to SuperCollider for flow-based playback."
  ([] (flow-connect! "127.0.0.1" 57110))
  ([host port]
   (reset! flow-client (osc/osc-client host port))
   (println "✓ Flow connected to" (str host ":" port))))

(defn flow-disconnect! []
  (when-let [client @flow-client]
    (osc/osc-close client)
    (reset! flow-client nil)
    (println "✓ Flow disconnected")))

;; ============================================================================
;; VALIDATION PREDICATES
;; ============================================================================

(defn valid-midi-range?
  "Check if all MIDI notes are in valid range (0-127)."
  [event]
  (let [freqs (get-in event [:audio :frequencies])]
    (if (seq freqs)
      (every? #(and (>= % 20) (<= % 20000)) freqs)  ; Valid freq range in Hz
      true)))

(defn valid-duration?
  "Check if event has positive duration."
  [event]
  (and (:dur event) (pos? (:dur event))))

(defn valid-amplitude?
  "Check if amplitude is in reasonable range."
  [event]
  (let [amp (get-in event [:audio :amplitude])]
    (or (nil? amp) (and (>= amp 0) (<= amp 1)))))

(defn valid-event?
  "Comprehensive event validation."
  [event]
  (and (valid-midi-range? event)
       (valid-duration? event)
       (valid-amplitude? event)))

;; ============================================================================
;; CORE FLOW ABSTRACTIONS
;; ============================================================================

(defn score->chan
  "Put score events onto a channel.
   Returns a channel that will receive all events, then close.
   Events are sorted by :at time before being placed on channel."
  ([score] (score->chan score (chan 32)))
  ([score out-chan]
   (let [events (sort-by :at (:events score))]
     (go
       (doseq [event events]
         (>! out-chan event))
       (close! out-chan)))
   out-chan))

(defn validate-flow
  "Filter channel through ontological validation.
   Invalid events are logged and dropped.
   Returns a new channel with only valid events."
  ([in-chan] (validate-flow in-chan (chan 32)))
  ([in-chan out-chan]
   (go-loop []
     (if-let [event (<! in-chan)]
       (do
         (if (valid-event? event)
           (>! out-chan event)
           (println "⚠ Invalid event dropped:" (:id event)))
         (recur))
       (close! out-chan)))
   out-chan))

(defn schedule-flow
  "Read events from channel, schedule with proper timing, play via OSC.
   This is the consumer that controls backpressure - it pulls events
   at the rate they should be played.
   
   Returns a channel that emits events as they are played (for monitoring)."
  ([tempo in-chan] (schedule-flow tempo in-chan (chan (sliding-buffer 16))))
  ([tempo in-chan played-chan]
   (go
     (let [start-time (System/nanoTime)
           beats->nanos (fn [beats]
                          (long (* (/ (* beats 60.0) tempo) 1e9)))]
       (loop []
         (when-let [event (<! in-chan)]
           (let [event-nanos (beats->nanos (:at event))
                 target-time (+ start-time event-nanos)
                 now (System/nanoTime)
                 wait-nanos (- target-time now)]
             ;; Wait until scheduled time
             (when (pos? wait-nanos)
               (<! (timeout (long (/ wait-nanos 1e6)))))
             ;; Play the event
             (when-let [client @flow-client]
               (let [audio (:audio event)
                     freqs (or (:frequencies audio) [440])
                     amp (or (:amplitude audio) 0.3)
                     dur-secs (/ (* (:dur event) 60.0) tempo)]
                 (doseq [freq freqs]
                   (osc/osc-send client "/s_new" "sine" -1 1 0
                                 "freq" (float freq)
                                 "amp" (float (/ amp (count freqs)))
                                 "sustain" (float dur-secs)))))
             ;; Emit played event for monitoring
             (>! played-chan event)
             (recur))))
       (close! played-chan)))
   played-chan))

;; ============================================================================
;; COMPOSABLE CURRICULUM FLOWS
;; ============================================================================

(defn pitch-class-flow
  "Generate a channel of pitch events from a world.
   Events flow out starting at start-beat."
  ([world] (pitch-class-flow world 0))
  ([world start-beat]
   (let [out-chan (chan 16)
         pitches (or (:pitch-classes world) (range 60 72))
         events (curriculum/pitch-class-events start-beat pitches 0.1 0.05)]
     (go
       (doseq [event events]
         (>! out-chan event))
       (close! out-chan))
     out-chan)))

(defn harmonic-function-flow
  "Generate a channel of harmonic function events.
   T→S→D progression as chord events."
  ([world] (harmonic-function-flow world 0))
  ([world start-beat]
   (let [out-chan (chan 8)
         functions (or (:harmonic-functions world)
                       [{:name "Tonic" :root 60 :chord [60 64 67]}
                        {:name "Subdominant" :root 65 :chord [65 69 72]}
                        {:name "Dominant" :root 67 :chord [67 71 74]}])
         events (curriculum/harmonic-function-events start-beat functions 0.8 0.4)]
     (go
       (doseq [event events]
         (>! out-chan event))
       (close! out-chan))
     out-chan)))

(defn modulation-flow
  "Generate a channel of modulation events (circle of fifths)."
  ([world] (modulation-flow world 0))
  ([world start-beat]
   (let [out-chan (chan 8)
         intervals (or (:modulation-keys world) [0 7 2 5])
         events (curriculum/modulation-events start-beat intervals 60 0.5 0.2)]
     (go
       (doseq [event events]
         (>! out-chan event))
       (close! out-chan))
     out-chan)))

(defn merge-flows
  "Merge multiple event channels into one, preserving temporal order.
   Collects all events, sorts by :at, then emits in order."
  [& chans]
  (let [out-chan (chan 64)]
    (go
      (let [all-events (atom [])]
        ;; Collect from all channels
        (doseq [ch chans]
          (loop []
            (when-let [event (<! ch)]
              (swap! all-events conj event)
              (recur))))
        ;; Sort and emit
        (doseq [event (sort-by :at @all-events)]
          (>! out-chan event))
        (close! out-chan)))
    out-chan))

(defn curriculum-flow
  "Create a merged flow of all curriculum sections from a world.
   Sections are offset to play sequentially:
   - Pitch classes: beat 0
   - Harmonic functions: beat 3  
   - Modulations: beat 8"
  [world]
  (merge-flows
   (pitch-class-flow world 0)
   (harmonic-function-flow world 3)
   (modulation-flow world 8)))

;; ============================================================================
;; HIGH-LEVEL PLAYBACK
;; ============================================================================

(defn play-curriculum!
  "Play the full curriculum using flow-based pipeline.
   
   Pipeline: score->chan -> validate-flow -> schedule-flow -> OSC
   
   Returns a channel that emits events as they play (for monitoring/testing)."
  ([world] (play-curriculum! world 120))
  ([world tempo]
   (flow-connect!)
   (let [score (curriculum/compile-full-curriculum tempo)
         events-chan (score->chan score)
         validated-chan (validate-flow events-chan)
         played-chan (schedule-flow tempo validated-chan)]
     ;; Return channel for monitoring; cleanup when done
     (go
       (loop []
         (when-let [event (<! played-chan)]
           (recur)))
       ;; Small delay to let final notes ring
       (<! (timeout 1000))
       (flow-disconnect!))
     played-chan)))

(defn play-initial-world!
  "Play just the initial world curriculum."
  ([] (play-initial-world! 120))
  ([tempo]
   (flow-connect!)
   (let [world core/initial-world
         events-chan (curriculum-flow world)
         validated-chan (validate-flow events-chan)
         played-chan (schedule-flow tempo validated-chan)]
     (go
       (loop []
         (when-let [event (<! played-chan)]
           (println "♪" (:id event) "@" (:at event))
           (recur)))
       (<! (timeout 1000))
       (flow-disconnect!))
     played-chan)))

(defn monitor-flow
  "Tap into a flow for monitoring without consuming.
   Returns [original-mult monitor-chan] where monitor-chan receives copies."
  [in-chan]
  (let [m (mult in-chan)
        monitor (chan (sliding-buffer 32))]
    (tap m monitor)
    [m monitor]))

;; ============================================================================
;; FLOW TRANSFORMERS (for composition)
;; ============================================================================

(defn transpose-flow
  "Transform flow by transposing all pitches by semitones."
  [semitones in-chan]
  (let [out-chan (chan 32)
        transpose-freq (fn [hz semis]
                         (* hz (Math/pow 2 (/ semis 12.0))))]
    (go-loop []
      (if-let [event (<! in-chan)]
        (let [transposed (update-in event [:audio :frequencies]
                                    (fn [freqs]
                                      (mapv #(transpose-freq % semitones) freqs)))]
          (>! out-chan transposed)
          (recur))
        (close! out-chan)))
    out-chan))

(defn amplify-flow
  "Scale amplitude of all events in flow."
  [scale in-chan]
  (let [out-chan (chan 32)]
    (go-loop []
      (if-let [event (<! in-chan)]
        (let [scaled (update-in event [:audio :amplitude] * scale)]
          (>! out-chan scaled)
          (recur))
        (close! out-chan)))
    out-chan))

(defn delay-flow
  "Offset all events by a number of beats."
  [beats in-chan]
  (let [out-chan (chan 32)]
    (go-loop []
      (if-let [event (<! in-chan)]
        (let [delayed (update event :at + beats)]
          (>! out-chan delayed)
          (recur))
        (close! out-chan)))
    out-chan))

;; ============================================================================
;; EXAMPLE COMPOSITIONS
;; ============================================================================

(defn canon-flow
  "Create a canon by layering the same material with delays and transpositions."
  [world delay-beats transpose-semis]
  (let [voice1 (curriculum-flow world)
        voice2 (-> (curriculum-flow world)
                   (delay-flow delay-beats)
                   (transpose-flow transpose-semis)
                   (amplify-flow 0.7))]
    (merge-flows voice1 voice2)))

(comment
  ;; Usage examples
  
  ;; Play full curriculum
  (play-curriculum! core/initial-world 120)
  
  ;; Play just initial world
  (play-initial-world! 100)
  
  ;; Create and play a canon
  (flow-connect!)
  (let [canon (canon-flow core/initial-world 2 7)  ; 2 beat delay, fifth up
        validated (validate-flow canon)
        played (schedule-flow 120 validated)]
    (go-loop []
      (when-let [e (<! played)]
        (println "♪" (:id e))
        (recur))))
  
  ;; Compose custom pipeline
  (flow-connect!)
  (-> (pitch-class-flow core/initial-world)
      (transpose-flow 12)  ; Up one octave
      (amplify-flow 0.5)
      (validate-flow)
      (schedule-flow 140))
  
  ;; Monitor what's playing
  (let [score (curriculum/compile-full-curriculum 120)
        events (score->chan score)
        [m monitor] (monitor-flow events)]
    (go-loop []
      (when-let [e (<! monitor)]
        (println "Event:" (:id e) "at beat" (:at e))
        (recur)))))
