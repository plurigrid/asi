(ns music-topos.runs-on
  "Module Action: Pattern Runs On Matter
   
   The key insight from Libkind & Spivak (ACT 2024):
   
   Ξ_{p,q} : 𝔪p ⊗ 𝔠q → 𝔪(p⊗q)
   
   This is the module action where:
   - 𝔪p is the free monad (Pattern/decision tree)
   - 𝔠q is the cofree comonad (Matter/behavior tree)  
   - The result 𝔪(p⊗q) combines pattern with matter's responses
   
   Musical interpretation:
   - Pattern (score) runs on Matter (performer/synth)
   - At each decision point, Matter provides a response
   - The wellfounded (finite) pattern consumes from the non-wellfounded (infinite) matter
   
   Backend: SuperCollider via Overtone/OSC (Clojure's native audio)
   
   Examples from the paper:
   - Interviews run on people
   - Programs run on operating systems
   - Games run on players
   - Musical scores run on performers"
  (:require [music-topos.free-monad :as free :refer [pure? run-free pure suspend
                                                      ->PlayNote ->PlayChord ->Rest
                                                      ->Transform ->Branch ->Sequence ->Parallel]]
            [music-topos.cofree-comonad :as cofree :refer [extract]]
            [music-topos.score :as score]
            [overtone.osc :as osc]))

;; ============================================================================
;; PAIRING: The Fundamental Connection
;; ============================================================================

;; A pairing between functors f and g is a natural transformation:
;;   pair : f a × g b → (a → b → c) → c
;;
;; It "zaps" a product into a result by:
;; - Taking a "question" from f
;; - Taking an "answer provider" from g  
;; - Combining question and answer

(defprotocol Pairable
  "Types that can be paired (zapped together)"
  (pair-with [f-val g-val combine]
    "Combine an f-value and g-value using the combine function"))

;; ============================================================================
;; INSTRUCTION-MATTER PAIRING
;; ============================================================================

(defn pair-instruction-matter
  "Pair a musical instruction (pattern) with matter (environment).
   
   The instruction asks a question, matter provides the answer.
   Returns: [result next-pattern next-matter]"
  [instruction matter combine]
  (cond
    ;; PlayNote: matter provides audio output and timing
    (instance? free/PlayNote instruction)
    (let [{:keys [pitch duration amplitude next]} instruction
          ;; Matter provides the actual playing capability
          play-fn (:play-fn matter (fn [p d a] (println "♪" p)))
          ;; Execute the note on matter
          _ (play-fn pitch duration amplitude)
          ;; Continue with next pattern
          next-pattern (next)]
      [nil next-pattern (update matter :beat + duration)])
    
    ;; PlayChord: similar but multiple pitches
    (instance? free/PlayChord instruction)
    (let [{:keys [pitches duration amplitude next]} instruction
          play-fn (:play-fn matter (fn [ps d a] (println "♪♪" ps)))]
      (play-fn pitches duration amplitude)
      [nil (next) (update matter :beat + duration)])
    
    ;; Rest: just advance time
    (instance? free/Rest instruction)
    (let [{:keys [duration next]} instruction]
      [nil (next) (update matter :beat + duration)])
    
    ;; Transform: matter provides the transformation result
    (instance? free/Transform instruction)
    (let [{:keys [transformation target next]} instruction
          ;; Matter knows how to apply transformations
          transform-fn (get-in matter [:transforms transformation] identity)
          result (transform-fn target)]
      [result (next result) matter])
    
    ;; Branch: matter provides the condition result
    (instance? free/Branch instruction)
    (let [{:keys [condition then-branch else-branch]} instruction
          ;; Matter knows the current context to evaluate condition
          condition-fn (get-in matter [:conditions condition] (constantly false))
          result (condition-fn matter)]
      [result (if result then-branch else-branch) matter])
    
    ;; Sequence: process each action, threading matter through
    (instance? free/Sequence instruction)
    (let [{:keys [actions]} instruction]
      [nil (pure actions) matter])  ; Return actions to be processed
    
    ;; Parallel: all voices run on same matter
    (instance? free/Parallel instruction)
    (let [{:keys [voices]} instruction]
      [nil (pure voices) matter])  ; Return voices to be processed
    
    :else
    (throw (ex-info "Unknown instruction type" {:instruction instruction}))))

;; ============================================================================
;; THE MODULE ACTION: runs-on
;; ============================================================================

(defn runs-on
  "The module action Ξ: Pattern runs on Matter.
   
   Given:
   - pattern: Free (musical instruction functor)
   - matter: Cofree (musical environment functor) OR simple matter state
   
   Returns:
   - A sequence of ScoreEvents representing the execution trace"
  [pattern matter]
  (loop [current-pattern pattern
         current-matter matter
         current-beat 0
         events []]
    (cond
      ;; Pattern complete (Pure value)
      (pure? current-pattern)
      events
      
      ;; More pattern to process
      :else
      (let [instruction (run-free current-pattern)
            [_result next-pattern next-matter] (pair-instruction-matter 
                                                 instruction 
                                                 current-matter
                                                 nil)]
        (cond
          ;; Handle Sequence: process each action
          (instance? free/Sequence instruction)
          (let [actions (:actions instruction)]
            (reduce (fn [[m b evs] action]
                      (let [sub-events (runs-on action m)
                            new-beat (+ b (reduce + 0 (map #(or (:dur %) 0) sub-events)))]
                        [(assoc m :beat new-beat) new-beat (into evs sub-events)]))
                    [current-matter current-beat events]
                    actions))
          
          ;; Handle Parallel: run all voices, collect events
          (instance? free/Parallel instruction)
          (let [voices (:voices instruction)
                all-events (mapcat #(runs-on % current-matter) voices)]
            (into events all-events))
          
          ;; Handle notes/chords: emit events
          (or (instance? free/PlayNote instruction)
              (instance? free/PlayChord instruction))
          (let [{:keys [pitch pitches duration amplitude]} instruction
                ps (or pitches [pitch])
                event (score/->ScoreEvent
                       (keyword (str "event-" (count events)))
                       current-beat
                       duration
                       {:world :pitch-space :type :note :value ps}
                       {:frequencies (mapv score/midi->hz ps)
                        :amplitude amplitude
                        :synth "sine"}
                       {:section :runs-on})]
            (recur (if (pure? next-pattern) next-pattern (pure nil))
                   (assoc next-matter :beat (+ current-beat duration))
                   (+ current-beat duration)
                   (conj events event)))
          
          ;; Handle rest: emit rest event
          (instance? free/Rest instruction)
          (let [event (score/->ScoreEvent
                       (keyword (str "rest-" (count events)))
                       current-beat
                       (:duration instruction)
                       {:world :rest-space :type :rest}
                       nil
                       {:section :runs-on})]
            (recur (if (pure? next-pattern) next-pattern (pure nil))
                   (assoc next-matter :beat (+ current-beat (:duration instruction)))
                   (+ current-beat (:duration instruction))
                   (conj events event)))
          
          ;; Other cases: continue
          :else
          (recur next-pattern next-matter current-beat events))))))

;; ============================================================================
;; SUPERCOLLIDER BACKEND (Clojure's native audio via Overtone)
;; ============================================================================

(def sc-client (atom nil))
(def node-id-counter (atom 1000))

(defn connect-supercollider!
  "Connect to SuperCollider server"
  ([] (connect-supercollider! "127.0.0.1" 57110))
  ([host port]
   (reset! sc-client (osc/osc-client host port))
   (println "✓ Connected to SuperCollider at" (str host ":" port))))

(defn next-node-id []
  (swap! node-id-counter inc))

(defn play-sine-sc!
  "Play a sine tone via SuperCollider"
  [freq amp dur]
  (when @sc-client
    (let [node-id (next-node-id)]
      (osc/osc-send @sc-client "/s_new" "sine" node-id 1 0
                    "freq" (float freq)
                    "amp" (float amp)
                    "sustain" (float dur)))))

(defn play-event-sc!
  "Play a ScoreEvent via SuperCollider"
  [event]
  (when-let [audio (:audio event)]
    (let [freqs (:frequencies audio)
          amp (or (:amplitude audio) 0.3)
          dur (or (:dur event) 1.0)]
      (doseq [freq freqs]
        (play-sine-sc! freq (/ amp (count freqs)) dur)))))

;; ============================================================================
;; PRACTICAL INTERPRETER
;; ============================================================================

(defn interpret-pattern
  "Interpret a musical pattern using provided matter.
   More practical version that handles real-time playback."
  [pattern matter play-fn]
  (let [matter-with-play (assoc matter :play-fn play-fn)]
    (loop [p pattern
           m matter-with-play]
      (when-not (pure? p)
        (let [instr (run-free p)
              [_ next-p next-m] (pair-instruction-matter instr m nil)]
          (when next-p
            (recur next-p next-m)))))))

;; ============================================================================
;; STREAMING INTERPRETER (for real-time)
;; ============================================================================

(defn pattern->event-stream
  "Convert a pattern into a lazy stream of events.
   Matter provides context at each step."
  [pattern matter-stream]
  (letfn [(step [p ms]
            (when-not (pure? p)
              (lazy-seq
               (let [m (first ms)
                     instr (run-free p)
                     [result next-p _] (pair-instruction-matter instr m nil)]
                 (cons {:instruction instr :matter m :result result}
                       (step next-p (rest ms)))))))]
    (step pattern matter-stream)))

;; ============================================================================
;; MODULE LAWS VERIFICATION
;; ============================================================================

(comment
  ;; The module structure satisfies:
  ;; 
  ;; 1. Associativity: (m ⊗ c) ⊗ c' ~ m ⊗ (c ⊗ c')
  ;;    Running pattern on (matter1 then matter2) = 
  ;;    Running pattern on matter1, then result on matter2
  ;;
  ;; 2. Unit: m ⊗ 1 ~ m
  ;;    Running pattern on trivial matter = pattern unchanged
  ;;
  ;; In musical terms:
  ;; - Playing a score with orchestra, then with effects processing
  ;;   = Playing with (orchestra + effects) combined
  ;; - Playing a score with "null performer" = the score structure itself
  )

;; ============================================================================
;; EXAMPLE USAGE
;; ============================================================================

(defn demo-runs-on
  "Demonstrate the module action"
  []
  (let [;; Simple pattern: C major arpeggio
        pattern (free/sequence!
                 (free/play-note! 60 0.5 0.3)  ; C
                 (free/play-note! 64 0.5 0.3)  ; E
                 (free/play-note! 67 0.5 0.3)  ; G
                 (free/play-note! 72 1.0 0.3)) ; C (octave up)
        
        ;; Simple matter: provides tempo and audio
        matter {:beat 0
                :tempo 120
                :timbre :sine
                :play-fn (fn [p d a] 
                           (println (format "Playing MIDI %d for %.2f beats at amp %.2f" 
                                            (if (coll? p) (first p) p) d a)))}
        
        ;; Run the pattern on matter
        events (runs-on pattern matter)]
    
    (println "\n=== Pattern Runs On Matter ===")
    (println "Generated" (count events) "events:")
    (doseq [e events]
      (println "  Beat" (:at e) "->" (get-in e [:audio :frequencies]) "Hz"))
    events))
