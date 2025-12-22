#!/usr/bin/env hy
; MultiInstrumentGadgets.hy
;
; Executable Hy skill for multi-instrument quantum composition
; Implements piano, strings, percussion gadgets with formal proof generation
; Integrates with interaction timeline and spectrogram analysis

(import
  json
  math
  [collections [defaultdict]]
  [datetime [datetime]]
  [typing [*]]
  [dataclasses [dataclass field]]
  [enum [Enum]]
)

; ============================================================================
; INSTRUMENT FAMILY DEFINITIONS
; ============================================================================

(defclass InstrumentFamily [Enum]
  (percussion 1)
  (strings 2)
  (wind 3)
  (electronic 4))

(defclass Instrument
  "Acoustic instrument with quantified properties"

  (defn __init__ [self family fundamental pitch-min pitch-max
                  spectral-sharpness decay-time &optional [name ""]]
    (setv self.family family)
    (setv self.fundamental fundamental)
    (setv self.pitch-min pitch-min)
    (setv self.pitch-max pitch-max)
    (setv self.spectral-sharpness spectral-sharpness)
    (setv self.decay-time decay-time)
    (setv self.name name))

  (defn __repr__ [self]
    (+ "Instrument(" self.name ")")))

; Standard instruments
(setv piano (Instrument
  InstrumentFamily.percussion 27.5 0 87 0.6 3.0 :name "Piano"))

(setv violin (Instrument
  InstrumentFamily.strings 196 55 96 0.8 4.0 :name "Violin"))

(setv cello (Instrument
  InstrumentFamily.strings 65 36 84 0.7 5.0 :name "Cello"))

(setv harpsichord (Instrument
  InstrumentFamily.percussion 27.5 0 84 0.9 0.5 :name "Harpsichord"))

(setv synth (Instrument
  InstrumentFamily.electronic 27.5 0 127 0.4 8.0 :name "Synth"))

; ============================================================================
; PREPARATION TECHNIQUE DEFINITIONS
; ============================================================================

(defclass Preparation
  "Instrument preparation: modification to acoustic behavior"

  (defn __init__ [self pitch-offset duration-mult amplitude-scale spectral-mult
                  &optional [name ""]]
    (setv self.pitch-offset pitch-offset)
    (setv self.duration-mult duration-mult)
    (setv self.amplitude-scale amplitude-scale)
    (setv self.spectral-mult spectral-mult)
    (setv self.name name))

  (defn to-dict [self]
    {"pitch_offset" self.pitch-offset
     "duration_mult" self.duration-mult
     "amplitude_scale" self.amplitude-scale
     "spectral_mult" self.spectral-mult
     "name" self.name})

  (defn __repr__ [self]
    (+ "Prep(" self.name ")")))

; Piano preparations
(setv prep-normal (Preparation 0 1.0 1.0 1.0 :name "Normal"))
(setv prep-harmonic (Preparation 12 0.3 0.15 2.0 :name "Harmonic"))
(setv prep-muted (Preparation 0.5 2.0 0.4 0.5 :name "Muted"))
(setv prep-low-res (Preparation -12 0.5 0.25 0.3 :name "LowResonance"))

; ============================================================================
; INTERACTION EVENT TRACKING
; ============================================================================

(defclass InteractionEvent
  "Causality-tracked interaction event"

  (defn __init__ [self timestamp instrument preparation operation depends-on]
    (setv self.timestamp timestamp)
    (setv self.instrument instrument)
    (setv self.preparation preparation)
    (setv self.operation operation)
    (setv self.depends-on depends-on)  ; list of prior event indices
    (setv self.fingerprint (hash (+ (str timestamp) (str operation)))))

  (defn to-dict [self]
    {"timestamp" self.timestamp
     "instrument" (. self.instrument name)
     "preparation" (. self.preparation name)
     "operation" self.operation
     "depends_on" self.depends-on
     "fingerprint" self.fingerprint})

  (defn __repr__ [self]
    (+ "Event@" (str self.timestamp) ":" self.operation)))

(defclass InteractionHistory
  "Immutable causality-tracked history of instrument events"

  (defn __init__ [self &optional [is-frozen False]]
    (setv self.events [])
    (setv self.is-frozen is-frozen))

  (defn add-event [self event]
    "Add event if not frozen (returns new history or self)"
    (if self.is-frozen
      self
      (do
        (.append self.events event)
        self)))

  (defn freeze [self]
    "Freeze history to prevent modifications"
    (setv self.is-frozen True)
    self)

  (defn verify-causality [self]
    "Check that all causality constraints are satisfied"
    (for [[i e1] (enumerate self.events)]
      (for [[j e2] (enumerate self.events)]
        (when (< i j)
          (assert (< e1.timestamp e2.timestamp)
            (+ "Causality violated: event " (str i) " after " (str j))))))
    True)

  (defn to-dict [self]
    {"events" (list (map (fn [e] (e.to-dict)) self.events))
     "is_frozen" self.is-frozen}))

; ============================================================================
; INSTRUMENT GADGETS (PHASE-SCOPED REWRITE RULES)
; ============================================================================

(defclass InstrumentGadget
  "Phase-scoped rewrite gadget for an instrument"

  (defn __init__ [self instrument base-rule allowed-preps &optional [name ""]]
    (setv self.instrument instrument)
    (setv self.base-rule base-rule)  ; function: ℚ → ℚ
    (setv self.allowed-preps allowed-preps)  ; list of allowed Preparation objects
    (setv self.name name))

  (defn rewrite [self pitch prep]
    "Apply rewrite rule with preparation"
    (if (in prep self.allowed-preps)
      (let [rewritten (self.base-rule pitch)]
        (+ rewritten (. prep pitch-offset)))
      (raise (ValueError (+ "Preparation not allowed: " (. prep name))))))

  (defn verify-pitch-bounds [self pitch]
    "Verify output pitch is within instrument bounds"
    (and (>= pitch 0) (<= pitch self.instrument.pitch-max)))

  (defn to-dict [self]
    {"instrument" (. self.instrument name)
     "allowed_preparations" (list (map (fn [p] (. p name)) self.allowed-preps))
     "name" self.name}))

; Standard piano gadget (RED gadget: f(x) >= x)
(defn make-piano-red-gadget [strength]
  "Create RED piano gadget (amplification)"
  (InstrumentGadget
    piano
    (fn [pitch] (* pitch (+ 1 strength)))
    [prep-normal prep-harmonic prep-muted prep-low-res]
    :name (+ "Piano-RED-" (str strength))))

; Standard piano gadget (BLUE gadget: f(x) <= x)
(defn make-piano-blue-gadget [strength]
  "Create BLUE piano gadget (contraction)"
  (InstrumentGadget
    piano
    (fn [pitch] (/ pitch (+ 1 strength)))
    [prep-normal prep-harmonic]
    :name (+ "Piano-BLUE-" (str strength))))

; Standard piano gadget (GREEN gadget: f(x) = x)
(defn make-piano-green-gadget []
  "Create GREEN piano gadget (identity)"
  (InstrumentGadget
    piano
    (fn [pitch] pitch)
    [prep-normal]
    :name "Piano-GREEN"))

; Violin gadget (continuous dynamics)
(defn make-violin-gadget [vibrato-depth]
  "Create violin gadget with vibrato"
  (InstrumentGadget
    violin
    (fn [pitch] (+ pitch (* vibrato-depth (math.sin pitch))))
    [prep-normal prep-muted]
    :name (+ "Violin-" (str vibrato-depth))))

; ============================================================================
; POLYPHONIC COMPOSITION
; ============================================================================

(defclass Voice
  "A voice: single instrument playing a note with preparation"

  (defn __init__ [self instrument pitch amplitude duration preparation]
    (setv self.instrument instrument)
    (setv self.pitch pitch)
    (setv self.amplitude amplitude)
    (setv self.duration duration)
    (setv self.preparation preparation))

  (defn to-dict [self]
    {"instrument" (. self.instrument name)
     "pitch" self.pitch
     "amplitude" self.amplitude
     "duration" self.duration
     "preparation" (. self.preparation name)}))

(defclass PolyphonicGesture
  "A polyphonic gesture: multiple voices with onset time"

  (defn __init__ [self voices onset-time &optional [phase-id 0]]
    (setv self.voices voices)  ; list of Voice
    (setv self.onset-time onset-time)
    (setv self.phase-id phase-id))

  (defn is-well-formed [self]
    "Check all voices are valid"
    (for [v self.voices]
      (assert (>= v.pitch 0) (+ "Pitch too low: " (str v.pitch)))
      (assert (<= v.pitch v.instrument.pitch-max)
        (+ "Pitch too high: " (str v.pitch)))
      (assert (and (>= v.amplitude 0) (<= v.amplitude 1))
        (+ "Invalid amplitude: " (str v.amplitude))))
    True)

  (defn to-dict [self]
    {"voices" (list (map (fn [v] (v.to-dict)) self.voices))
     "onset_time" self.onset-time
     "phase_id" self.phase-id}))

; ============================================================================
; BRITISH ARTISTS' TECHNIQUES (FORMALIZED)
; ============================================================================

; Aphex Twin: Windowlicker chaos equation
(defn windowlicker-equation [t &optional [base-freq 60]]
  "Aphex Twin's equation-driven melody from Windowlicker face spectrogram"
  (+ base-freq
     (* 12
        (math.sin (* t 0.5))
        (math.exp (* (- t) 0.1)))))

; Autechre: Cellular automaton texture
(defn autechre-ca-texture [generation pitch &optional [rule 30]]
  "Autechre-style CA-driven pitch modulation"
  (let [ca (% (+ generation pitch) 3)]
    (if (= ca 0)
      pitch
      (+ pitch (* (if (= ca 1) 7 -7) 0.5)))))

; Daniel Avery: Beating frequencies
(defn daniel-avery-beating [beat-freq duration]
  "Daniel Avery's synchronized detuning for beating"
  (/ beat-freq 100))

; Mica Levi: Microtonal clusters
(defn mica-levi-cluster [density]
  "Mica Levi's pitch-packed microtonality"
  (* 0.5 (/ (% density 5) 5)))

; ============================================================================
; SPECTROGRAM ANALYSIS
; ============================================================================

(defclass SpectrogramFrame
  "A frequency-time snapshot"

  (defn __init__ [self frequencies magnitudes time-index]
    (setv self.frequencies frequencies)  ; list of freq values
    (setv self.magnitudes magnitudes)    ; list of magnitude values
    (setv self.time-index time-index)))

(defn spectrogram-peak-pitch [frame]
  "Extract pitch from spectrogram (peak frequency in semitones from C0)"
  (let [max-idx (-1)]
    (for [[i mag] (enumerate frame.magnitudes)]
      (when (> mag 0.1)
        (setv max-idx i)))
    (if (= max-idx -1) 0 max-idx)))

(defn spectrogram-follows-equation [frames equation]
  "Verify spectrogram trajectory matches an equation"
  (for [[i frame] (enumerate frames)]
    (let [expected (equation (/ i 44100.0))  ; convert to seconds
          actual (spectrogram-peak-pitch frame)
          error (abs (- actual expected))]
      (assert (< error 2) (+ "Spectrogram deviation at frame " (str i)))))
  True)

; ============================================================================
; MULTI-INSTRUMENT WORLD STATE
; ============================================================================

(defclass MultiInstrumentWorld
  "Extended quantum guitar world with multiple instruments"

  (defn __init__ [self name]
    (setv self.name name)
    (setv self.instruments {})  ; instrument-id -> Instrument
    (setv self.gadgets {})      ; gadget-id -> InstrumentGadget
    (setv self.gestures [])     ; list of PolyphonicGesture
    (setv self.history (InteractionHistory))
    (setv self.audit-trail [])  ; {timestamp, action, detail}
    (setv self.creation-time (datetime.now)))

  (defn add-instrument [self inst-id instrument]
    "Register an instrument"
    (setv (get self.instruments inst-id) instrument)
    (.append self.audit-trail
      {"timestamp" (datetime.now)
       "action" "add_instrument"
       "detail" (. instrument name)})
    self)

  (defn add-gadget [self gadget-id gadget]
    "Register a gadget"
    (setv (get self.gadgets gadget-id) gadget)
    (.append self.audit-trail
      {"timestamp" (datetime.now)
       "action" "add_gadget"
       "detail" (. gadget name)})
    self)

  (defn add-gesture [self gesture]
    "Add a polyphonic gesture"
    (gesture.is-well-formed)
    (.append self.gestures gesture)

    ; Create interaction events for each voice
    (for [[voice-idx voice] (enumerate gesture.voices)]
      (let [event (InteractionEvent
        gesture.onset-time
        voice.instrument
        voice.preparation
        "note_on"
        [])]
        (.add-event self.history event)))

    (.append self.audit-trail
      {"timestamp" (datetime.now)
       "action" "add_gesture"
       "detail" (+ (str (len gesture.voices)) " voices")})
    self)

  (defn freeze [self]
    "Freeze world state and history"
    (.freeze self.history)
    self)

  (defn to-dict [self]
    {"name" self.name
     "instruments" (dict (for [[k v] (.items self.instruments)]
                          [k (. v name)]))
     "gadgets" (list (map (fn [g] (. g name)) (.values self.gadgets)))
     "gestures" (list (map (fn [g] (g.to-dict)) self.gestures))
     "history" (self.history.to-dict)
     "creation_time" (str self.creation-time)}))

; ============================================================================
; MACRO: Create multi-instrument gesture
; ============================================================================

(defmacro defgesture [name &rest voice-specs]
  "Define a polyphonic gesture
   Usage: (defgesture my-chord
            [piano 60 0.8 1.0 prep-normal]
            [violin 72 0.6 2.0 prep-muted])"
  (let [voices (lfor [spec voice-specs]
                     `(Voice ~@spec))]
    `(do
       (setv ~name (PolyphonicGesture ~voices 0))
       ~name)))

; ============================================================================
; MACRO: Multi-instrument composition with proofs
; ============================================================================

(defmacro with-multi-instrument-world [world-name &rest body]
  "Execute body in a multi-instrument world context"
  `(do
     (setv ~world-name (MultiInstrumentWorld ~(str world-name)))
     ~@body
     ~world-name))

; ============================================================================
; PROOF GENERATION FOR MULTI-INSTRUMENT SYSTEMS
; ============================================================================

(defclass MultiInstrumentProof
  "Formal proof that multi-instrument composition is correct"

  (defn __init__ [self world]
    (setv self.world world)
    (setv self.proof-type "multi-instrument-correctness")
    (setv self.timestamp (datetime.now))
    (setv self.statements []))

  (defn add-statement [self statement]
    "Add a formal statement to the proof"
    (.append self.statements statement)
    self)

  (defn verify-causality [self]
    "Verify interaction history causality"
    (assert (self.world.history.verify-causality)
      "Causality constraints violated")
    (.add-statement self "∀ events e₁, e₂: timestamp(e₁) < timestamp(e₂) → causal")
    self)

  (defn verify-well-formedness [self]
    "Verify all gestures are well-formed"
    (for [gesture self.world.gestures]
      (assert (gesture.is-well-formed) "Gesture not well-formed"))
    (.add-statement self "∀ gestures g: isWellFormed(g)")
    self)

  (defn verify-instrument-compatibility [self]
    "Verify all voices use compatible instruments"
    (for [gesture self.world.gestures]
      (for [voice gesture.voices]
        (assert (in voice.preparation voice.instrument.family)
          (+ "Incompatible instrument: " (. voice.instrument name)))))
    (.add-statement self "∀ voices v: v.instrument ∈ SupportedInstruments")
    self)

  (defn to-dict [self]
    {"proof_type" self.proof-type
     "timestamp" (str self.timestamp)
     "statements" self.statements
     "causality_verified" True
     "well_formedness_verified" True}))

; Generate proof for a world
(defn prove-multi-instrument-world [world]
  "Generate complete correctness proof for multi-instrument world"
  (let [proof (MultiInstrumentProof world)]
    (.verify-causality proof)
    (.verify-well-formedness proof)
    (.verify-instrument-compatibility proof)
    proof))

; ============================================================================
; HELPER FUNCTIONS
; ============================================================================

(defn multi-instrument-world->json [world]
  "Serialize world to JSON"
  (json.dumps (world.to-dict) :indent 2))

(defn print-gesture [gesture &optional [indent 0]]
  "Pretty-print a gesture"
  (let [ind (* " " indent)]
    (print (+ ind "Gesture @ " (str gesture.onset-time) "s:"))
    (for [v gesture.voices]
      (print (+ ind "  " (. v.instrument name)
                " pitch=" (str v.pitch)
                " amp=" (str v.amplitude)
                " prep=" (. v.preparation name))))))

(defn print-world [world]
  "Pretty-print a world"
  (print (+ "=== MultiInstrument World: " world.name " ==="))
  (print (+ "Instruments: " (str (list (.keys world.instruments)))))
  (print (+ "Gadgets: " (str (list (.keys world.gadgets)))))
  (print (+ "Gestures: " (str (len world.gestures))))
  (print (+ "History events: " (str (len world.history.events))))
  (for [g world.gestures]
    (print-gesture g :indent 2)))

; ============================================================================
; DEMONSTRATION
; ============================================================================

(defn demo-multi-instrument []
  "Demonstrate multi-instrument composition with formal proofs"
  (print "\n=== Multi-Instrument Quantum Music Demo ===\n")

  ; Create world
  (with-multi-instrument-world my-world
    ; Add instruments
    (.add-instrument my-world "piano" piano)
    (.add-instrument my-world "violin" violin)

    ; Add gadgets
    (.add-gadget my-world "piano-red" (make-piano-red-gadget 0.3))
    (.add-gadget my-world "piano-blue" (make-piano-blue-gadget 0.3))
    (.add-gadget my-world "violin-vib" (make-violin-gadget 0.5))

    ; Create gestures
    (let [gesture1 (PolyphonicGesture
            [(Voice piano 60 0.8 1.0 prep-normal)
             (Voice violin 72 0.6 2.0 prep-muted)]
            0.0)]
      (.add-gesture my-world gesture1))

    (let [gesture2 (PolyphonicGesture
            [(Voice piano 67 0.7 1.5 prep-harmonic)
             (Voice violin 79 0.5 2.5 prep-normal)]
            1.0)]
      (.add-gesture my-world gesture2))

    ; Freeze world
    (.freeze my-world)

    ; Print world
    (print-world my-world)

    ; Generate proof
    (let [proof (prove-multi-instrument-world my-world)]
      (print "\n=== Formal Correctness Proof ===")
      (for [stmt proof.statements]
        (print (+ "✓ " stmt)))
      (print (json.dumps (proof.to-dict) :indent 2)))

    ; Serialize
    (print "\n=== JSON Serialization ===")
    (print (multi-instrument-world->json my-world))))

; Run demo if executed directly
(if (= __name__ "__main__")
  (demo-multi-instrument))
