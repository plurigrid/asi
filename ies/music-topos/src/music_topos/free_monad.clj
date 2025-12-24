(ns music-topos.free-monad
  "Free Monad (Pattern) - Decision trees for musical actions.
   
   Based on Libkind & Spivak's 'Pattern Runs on Matter' (ACT 2024):
   - Free monad 𝔪p represents terminating decision trees
   - Pattern determines how a situation can unfold
   - Each position is a question, directions are possible answers
   
   Musical interpretation:
   - Pattern = the score/composition structure
   - Positions = musical choices (which note, which chord, which transformation)
   - Directions = specific instantiations of those choices"
  (:require [clojure.core.async :as async]))

;; ============================================================================
;; FREE MONAD DATA STRUCTURE
;; ============================================================================

;; Free f a = Pure a | Free (f (Free f a))
;; 
;; For music: f is the "instruction functor" - what musical operations exist
;; Pure = computation complete, return a value
;; Free = perform an operation, continue with the result

(defprotocol IFree
  "Protocol for free monad values"
  (pure? [this] "Is this a Pure value?")
  (run-free [this] "Extract the wrapped value or functor"))

(defrecord Pure [value]
  IFree
  (pure? [_] true)
  (run-free [this] (:value this)))

(defrecord Suspend [functor]
  IFree
  (pure? [_] false)
  (run-free [this] (:functor this)))

;; Smart constructors
(defn pure [x] (->Pure x))
(defn suspend [f] (->Suspend f))

;; ============================================================================
;; MUSICAL INSTRUCTION FUNCTOR
;; ============================================================================

;; The functor F for musical operations
;; Each constructor represents a musical "question" with continuations

(defrecord PlayNote [pitch duration amplitude next]
  ;; Play a single note, then continue
  ;; pitch: MIDI note number
  ;; duration: beats  
  ;; amplitude: 0-1
  ;; next: () -> Free F a (continuation after note plays)
  )

(defrecord PlayChord [pitches duration amplitude next]
  ;; Play multiple notes simultaneously
  ;; pitches: vector of MIDI notes
  ;; next: () -> Free F a
  )

(defrecord Rest [duration next]
  ;; Silent pause
  ;; next: () -> Free F a
  )

(defrecord Transform [transformation target next]
  ;; Apply a musical transformation (morphism in the topos)
  ;; transformation: keyword (:transpose, :invert, :retrograde, :plr-L, :plr-P, :plr-R)
  ;; target: the musical object to transform
  ;; next: (result) -> Free F a (continuation receives the transformed object)
  )

(defrecord Branch [condition then-branch else-branch]
  ;; Decision point based on musical context
  ;; condition: keyword for what to check (:in-tonic?, :cadence-ready?, etc.)
  ;; then-branch, else-branch: Free F a
  )

(defrecord Sequence [actions]
  ;; Sequential composition of multiple Free values
  ;; actions: vector of Free F a
  )

(defrecord Parallel [voices]
  ;; Parallel composition (polyphony)
  ;; voices: vector of Free F a to execute simultaneously
  )

;; ============================================================================
;; FUNCTOR INSTANCE (fmap)
;; ============================================================================

(defn fmap-instruction
  "Apply f to the continuation(s) of a musical instruction"
  [f instr]
  (condp instance? instr
    PlayNote   (->PlayNote (:pitch instr) (:duration instr) (:amplitude instr)
                           (comp f (:next instr)))
    PlayChord  (->PlayChord (:pitches instr) (:duration instr) (:amplitude instr)
                            (comp f (:next instr)))
    Rest       (->Rest (:duration instr) (comp f (:next instr)))
    Transform  (->Transform (:transformation instr) (:target instr)
                            (comp f (:next instr)))
    Branch     (->Branch (:condition instr) (f (:then-branch instr)) (f (:else-branch instr)))
    Sequence   (->Sequence (mapv f (:actions instr)))
    Parallel   (->Parallel (mapv f (:voices instr)))))

;; ============================================================================
;; MONAD INSTANCE
;; ============================================================================

(defn free-bind
  "Monadic bind for Free monad: Free f a -> (a -> Free f b) -> Free f b"
  [free-val f]
  (if (pure? free-val)
    (f (run-free free-val))
    (suspend (fmap-instruction #(free-bind % f) (run-free free-val)))))

(defn free-map
  "Functor map for Free monad"
  [f free-val]
  (free-bind free-val (comp pure f)))

(defn free-flatten
  "Join/flatten: Free f (Free f a) -> Free f a"
  [nested]
  (free-bind nested identity))

;; ============================================================================
;; DSL CONSTRUCTORS (lift instructions into Free)
;; ============================================================================

(defn play-note!
  "DSL: Play a note and continue"
  [pitch duration amplitude]
  (suspend (->PlayNote pitch duration amplitude (fn [] (pure nil)))))

(defn play-chord!
  "DSL: Play a chord and continue"
  [pitches duration amplitude]
  (suspend (->PlayChord pitches duration amplitude (fn [] (pure nil)))))

(defn rest!
  "DSL: Rest for a duration and continue"
  [duration]
  (suspend (->Rest duration (fn [] (pure nil)))))

(defn transform!
  "DSL: Apply transformation and receive result"
  [transformation target]
  (suspend (->Transform transformation target (fn [result] (pure result)))))

(defn branch!
  "DSL: Branch based on a condition"
  [condition then-branch else-branch]
  (suspend (->Branch condition then-branch else-branch)))

(defn sequence!
  "DSL: Sequential composition"
  [& actions]
  (suspend (->Sequence (vec actions))))

(defn parallel!
  "DSL: Parallel composition (polyphony)"
  [& voices]
  (suspend (->Parallel (vec voices))))

;; ============================================================================
;; EXAMPLE: INITIAL WORLD AS FREE MONAD
;; ============================================================================

(defn initial-world-pattern
  "The Initial World curriculum as a Free monad pattern (decision tree)"
  []
  (sequence!
   ;; 1. Initial pitch
   (play-note! 60 2.0 0.3)
   
   ;; 2. Chromatic scale (all 12 pitch classes)
   (sequence!
    (play-note! 60 0.08 0.2)
    (play-note! 61 0.08 0.2)
    (play-note! 62 0.08 0.2)
    (play-note! 63 0.08 0.2)
    (play-note! 64 0.08 0.2)
    (play-note! 65 0.08 0.2)
    (play-note! 66 0.08 0.2)
    (play-note! 67 0.08 0.2)
    (play-note! 68 0.08 0.2)
    (play-note! 69 0.08 0.2)
    (play-note! 70 0.08 0.2)
    (play-note! 71 0.08 0.2))
   
   ;; 3. Harmonic functions T → S → D → T
   (sequence!
    (play-chord! [60 64 67] 0.8 0.2)  ; Tonic (C major)
    (play-chord! [65 69 72] 0.8 0.2)  ; Subdominant (F major)
    (play-chord! [67 71 74] 0.8 0.2)  ; Dominant (G major)
    (play-chord! [60 64 67] 0.8 0.2)) ; Return to Tonic
   
   ;; 4. Circle of fifths modulation
   (sequence!
    (play-note! 60 0.5 0.25)  ; C
    (play-note! 67 0.5 0.25)  ; G (fifth up)
    (play-note! 62 0.5 0.25)  ; D (fifth up from G, mod 12)
    (play-note! 69 0.5 0.25)))) ; A

;; ============================================================================
;; ITERATEE / FOLD
;; ============================================================================

(defn fold-free
  "Fold a free monad given an interpreter for the functor.
   interpreter: F a -> M a (where M is some monad, e.g., IO or State)
   Returns the final value after running all instructions."
  [interpreter free-val]
  (if (pure? free-val)
    (run-free free-val)
    (interpreter (fmap-instruction #(fold-free interpreter %) (run-free free-val)))))

;; ============================================================================
;; PAIRING TYPE (for module structure with Cofree)
;; ============================================================================

(defprotocol IPairing
  "Pairing between functors f and g: (a -> b -> c) -> f a -> g b -> c
   This enables the module action: Free f ⊗ Cofree g → Free (f ⊗ g)"
  (pair [this combine f-val g-val]))

;; The pairing will be implemented when we create the Cofree comonad
;; It represents: for each question (f position), matter provides an answer (g direction)
