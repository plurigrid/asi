(ns music-topos.cofree-comonad
  "Cofree Comonad (Matter) - Behavior trees / environments.
   
   Based on Libkind & Spivak's 'Pattern Runs on Matter' (ACT 2024):
   - Cofree comonad 𝔠q represents q-behavior trees (non-terminating)
   - Matter responds with decisions at each juncture
   - Positions are observations, directions lead to future states
   
   Musical interpretation:
   - Matter = the performer/synthesizer/environment
   - Each position = current observable state (tempo, timbre, volume, context)
   - Each direction = a possible future based on what happens next
   
   The cofree comonad memoizes all possible futures of a comonadic machine."
  (:require [music-topos.free-monad :as free]))

;; ============================================================================
;; COFREE COMONAD DATA STRUCTURE
;; ============================================================================

;; Cofree f a = a :< f (Cofree f a)
;;
;; - The 'a' is the current observable value (what we can extract)
;; - The 'f (Cofree f a)' is a functorful of possible futures
;;
;; Think of it as an infinite tree where:
;; - Each node stores an observation
;; - Each branch leads to a subtree of future observations

(defrecord Cofree [head tail]
  ;; head: a (current observation)
  ;; tail: f (Cofree f a) (functorful of futures)
  )

;; Smart constructor
(defn cofree [head tail]
  (->Cofree head tail))

;; ============================================================================
;; COMONAD OPERATIONS
;; ============================================================================

(defn extract
  "Extract the current observation from a Cofree value.
   This is counit: Cofree f a -> a"
  [cf]
  (:head cf))

(defn extend
  "Extend a function over all positions in the Cofree structure.
   (Cofree f a -> b) -> Cofree f a -> Cofree f b"
  [f cf fmap-tail]
  (cofree (f cf)
          (fmap-tail #(extend f % fmap-tail) (:tail cf))))

(defn duplicate
  "Duplicate the Cofree structure so each position contains the subtree rooted there.
   Cofree f a -> Cofree f (Cofree f a)"
  [cf fmap-tail]
  (extend identity cf fmap-tail))

;; ============================================================================
;; MUSICAL ENVIRONMENT FUNCTOR
;; ============================================================================

;; The functor for musical environment/matter
;; Each represents a way the environment can respond

(defrecord TempoResponse [bpm continue]
  ;; Response: provide current tempo
  ;; bpm: current beats per minute
  ;; continue: Cofree with future state
  )

(defrecord TimbreResponse [timbre continue]
  ;; Response: provide current timbre/instrument
  ;; timbre: keyword like :sine, :piano, :strings
  ;; continue: Cofree with future state
  )

(defrecord VolumeResponse [volume continue]
  ;; Response: provide current volume
  ;; volume: 0-1
  ;; continue: Cofree with future state
  )

(defrecord HarmonicContext [current-key current-function continue]
  ;; Response: provide harmonic context
  ;; current-key: e.g., :C-major, :G-minor
  ;; current-function: :tonic, :subdominant, :dominant
  ;; continue: Cofree with future state
  )

(defrecord TimePosition [beat measure continue]
  ;; Response: provide current time position
  ;; beat: current beat within measure
  ;; measure: current measure number
  ;; continue: Cofree with future state
  )

(defrecord AudioOutput [play-fn continue]
  ;; Response: provide audio output capability
  ;; play-fn: function to actually produce sound
  ;; continue: Cofree with future state
  )

;; Composite environment: all musical context together
(defrecord MusicalMatter [tempo timbre volume harmonic-ctx time-pos audio]
  ;; The complete musical environment
  ;; Each field can be queried by Pattern
  )

;; ============================================================================
;; FUNCTOR INSTANCE FOR ENVIRONMENT
;; ============================================================================

(defn fmap-matter
  "Apply f to the continuation of a matter response"
  [f matter]
  (condp instance? matter
    TempoResponse    (->TempoResponse (:bpm matter) (f (:continue matter)))
    TimbreResponse   (->TimbreResponse (:timbre matter) (f (:continue matter)))
    VolumeResponse   (->VolumeResponse (:volume matter) (f (:continue matter)))
    HarmonicContext  (->HarmonicContext (:current-key matter) (:current-function matter) 
                                        (f (:continue matter)))
    TimePosition     (->TimePosition (:beat matter) (:measure matter) (f (:continue matter)))
    AudioOutput      (->AudioOutput (:play-fn matter) (f (:continue matter)))
    MusicalMatter    (->MusicalMatter (f (:tempo matter)) (f (:timbre matter))
                                       (f (:volume matter)) (f (:harmonic-ctx matter))
                                       (f (:time-pos matter)) (f (:audio matter)))))

;; ============================================================================
;; COITERATION - Building Cofree from a seed
;; ============================================================================

(defn coiter
  "Coiterate: build a Cofree from a seed value.
   Given a -> f a (unfold step), build the infinite Cofree structure.
   
   (a -> f a) -> a -> Cofree f a"
  [psi seed fmap-f]
  (cofree seed (fmap-f #(coiter psi % fmap-f) (psi seed))))

(defn unfold-matter
  "Unfold musical matter from initial state.
   Creates an infinite behavior tree of all possible futures."
  [initial-state state->next-states fmap-f]
  (coiter state->next-states initial-state fmap-f))

;; ============================================================================
;; SIMPLE MUSICAL MATTER EXAMPLE
;; ============================================================================

(defn simple-audio-matter
  "Create a simple matter that just provides audio output.
   Uses a play function and maintains state across time."
  [play-fn initial-beat tempo]
  (letfn [(unfold-step [state]
            (->AudioOutput 
             play-fn
             (assoc state :beat (inc (:beat state)))))]
    (coiter unfold-step
            {:beat initial-beat :tempo tempo}
            (fn [f audio-output]
              (->AudioOutput (:play-fn audio-output)
                             (f (:continue audio-output)))))))

;; ============================================================================
;; STREAMING MATTER - Infinite environment as lazy sequence
;; ============================================================================

(defn matter-stream
  "Create a lazy stream of matter states.
   This is a practical representation for real-time systems."
  [initial-state step-fn]
  (iterate step-fn initial-state))

(defn make-performance-matter
  "Create matter for a musical performance.
   Returns an infinite stream of environment states."
  [{:keys [tempo timbre volume] :or {tempo 90 timbre :sine volume 0.5}}]
  (matter-stream
   {:beat 0
    :tempo tempo
    :timbre timbre
    :volume volume
    :time-ns (System/nanoTime)}
   (fn [state]
     (let [beat-duration-ns (* (/ 60.0 (:tempo state)) 1e9)]
       (-> state
           (update :beat inc)
           (assoc :time-ns (+ (:time-ns state) (long beat-duration-ns))))))))

;; ============================================================================
;; LENSES INTO COFREE
;; ============================================================================

(defn unwrap
  "Unfocus from Cofree, getting the tail functor"
  [cf]
  (:tail cf))

(defn telescope
  "Get a path through the Cofree structure.
   selector: a function that picks which branch at each level
   Returns a lazy sequence of the heads along that path."
  [cf selector]
  (lazy-seq
   (cons (extract cf)
         (when-let [next-cf (selector (:tail cf))]
           (telescope next-cf selector)))))
