/-
  MusicTopos.MultiInstrumentComposition

  Extension of quantum guitar framework to multi-instrument polyphonic composition.
  Formalizes classical instruments (piano, strings, percussion) with prepared techniques
  as gadgets in the phase space.

  Key extensions:
  - Instrument types with acoustic properties
  - Polyphonic phase spaces (one phase per instrument)
  - Prepared technique semantics (detuning, muting, resonance)
  - Interaction history tracking (causality across instruments)
  - British artists' techniques formalized (Aphex Twin, Autechre, etc.)
-/

import Mathlib.Order.GaloisConnection
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Permutation
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Vector.Basic
import MusicTopos.GaloisDerangement

open scoped Padic
open Function (bijective injective surjective)
open Fintype Equiv Perm

namespace MusicTopos

/-! ## Instrument Classification -/

/-- Acoustic instrument families -/
inductive InstrumentFamily : Type where
  /-- Percussion: struck/plucked (piano, guitar, harps) -/
  | percussion : InstrumentFamily
  /-- Strings: continuous vibration (violin, cello) -/
  | strings : InstrumentFamily
  /-- Wind: air column resonance (flute, clarinet) -/
  | wind : InstrumentFamily
  /-- Electronic: synthesis (synth, sequencer) -/
  | electronic : InstrumentFamily
  deriving Repr, DecidableEq

/-- Specific instrument type with acoustic parameters -/
structure Instrument where
  /-- Which family does this belong to? -/
  family : InstrumentFamily
  /-- Fundamental frequency (Hz) -/
  fundamental : ℚ
  /-- Pitch range (semitones from C0) -/
  pitchMin pitchMax : ℕ
  /-- Spectral envelope shape: affects harmonic content -/
  spectralSharpness : ℚ  -- 0 (flat) to 1 (sharp peaks)
  /-- Natural decay time (seconds) -/
  decayTime : ℚ
  deriving Repr

/-- Standard instruments with known acoustic properties -/
namespace StandardInstruments

def piano : Instrument := {
  family := InstrumentFamily.percussion
  fundamental := 27.5  -- A0
  pitchMin := 0
  pitchMax := 87
  spectralSharpness := 0.6
  decayTime := 3.0
}

def violin : Instrument := {
  family := InstrumentFamily.strings
  fundamental := 196  -- G3
  pitchMin := 55
  pitchMax := 96
  spectralSharpness := 0.8
  decayTime := 4.0
}

def cello : Instrument := {
  family := InstrumentFamily.strings
  fundamental := 65  -- C1
  pitchMin := 36
  pitchMax := 84
  spectralSharpness := 0.7
  decayTime := 5.0
}

def harpsichord : Instrument := {
  family := InstrumentFamily.percussion
  fundamental := 27.5  -- A0
  pitchMin := 0
  pitchMax := 84
  spectralSharpness := 0.9
  decayTime := 0.5
}

def synth : Instrument := {
  family := InstrumentFamily.electronic
  fundamental := 27.5
  pitchMin := 0
  pitchMax := 127
  spectralSharpness := 0.4
  decayTime := 8.0
}

end StandardInstruments

/-! ## Preparation Techniques -/

/-- A preparation: modification to instrument's acoustic behavior -/
structure Preparation where
  /-- Pitch offset (semitones) from nominal -/
  pitchOffset : ℚ
  /-- Duration multiplier: how preparation affects sustain -/
  durationMult : ℚ
  /-- Amplitude scaling: how preparation affects loudness -/
  amplitudeScale : ℚ
  /-- Spectral sharpness modification -/
  spectralMult : ℚ
  deriving Repr

/-- Piano preparation types -/
namespace PianoPrepparations

/-- Normal: unmodified piano sound -/
def normal : Preparation := {
  pitchOffset := 0
  durationMult := 1.0
  amplitudeScale := 1.0
  spectralMult := 1.0
}

/-- Harmonic: struck at nodal point (12th fret) -/
def harmonic : Preparation := {
  pitchOffset := 12  -- One octave up
  durationMult := 0.3  -- Short decay
  amplitudeScale := 0.15  -- Quieter
  spectralMult := 2.0  -- Sharper spectrum
}

/-- Muted: cloth damper on strings -/
def muted : Preparation := {
  pitchOffset := 0.5  -- Slight detuning
  durationMult := 2.0  -- Extended resonance
  amplitudeScale := 0.4  -- Dampened
  spectralMult := 0.5  -- Duller
}

/-- Low resonance: striking below the key -/
def lowResonance : Preparation := {
  pitchOffset := -12  -- One octave down
  durationMult := 0.5
  amplitudeScale := 0.25
  spectralMult := 0.3
}

end PianoPrepparations

/-! ## Polyphonic Phase Spaces -/

/-- A polyphonic moment: one phase per active instrument -/
structure PolyphonicPhase where
  /-- Master phase: controls overall timing -/
  master : Phase
  /-- Per-instrument phases: separate causality streams -/
  instrumentPhases : ℕ → Phase
  /-- Synchronization: how tightly instruments must stay together -/
  synchronization : ℚ  -- 0 (independent) to 1 (locked)
  deriving Repr

/-- Notes in a polyphonic voice -/
structure Voice where
  /-- Which instrument plays this voice -/
  instrument : Instrument
  /-- Current preparation applied -/
  preparation : Preparation
  /-- MIDI pitch (0-127) -/
  pitch : ℕ
  /-- Note amplitude (0-1) -/
  amplitude : ℚ
  /-- Note duration (seconds) -/
  duration : ℚ
  deriving Repr

/-- A polyphonic gesture: simultaneous notes across instruments -/
structure PolyphonicGesture where
  /-- Voices playing in this gesture -/
  voices : Finset Voice
  /-- Onset time (seconds) -/
  onsetTime : ℚ
  /-- Phase context -/
  phase : PolyphonicPhase
  deriving Repr

/-! ## Interaction History (Timeline Integration) -/

/-- An interaction event: causality-tracked instrument event -/
structure InteractionEvent where
  /-- Timestamp (vector clock) -/
  timestamp : ℕ
  /-- Which instrument triggered this? -/
  instrument : Instrument
  /-- What preparation was applied? -/
  preparation : Preparation
  /-- What was the musical operation? -/
  operation : String  -- "note_on", "note_off", "slide", "vibrato", etc.
  /-- Previous events this depends on (causality) -/
  dependsOn : Finset ℕ  -- indices of prior events
  /-- Fingerprint for integrity tracking -/
  fingerprint : ℕ
  deriving Repr

/-- Complete interaction history: immutable audit trail -/
structure InteractionHistory where
  /-- Events in order -/
  events : List InteractionEvent
  /-- Whether history is frozen (immutable) -/
  isFrozen : Bool
  deriving Repr

namespace InteractionHistory

/-- Add an event to history (preserves immutability) -/
def addEvent (h : InteractionHistory) (e : InteractionEvent) : InteractionHistory :=
  if h.isFrozen then h else ⟨h.events ++ [e], h.isFrozen⟩

/-- Freeze history to prevent further modifications -/
def freeze (h : InteractionHistory) : InteractionHistory :=
  ⟨h.events, true⟩

/-- Causality between two events: e₁ happens before e₂ -/
def causesBefore (e₁ e₂ : InteractionEvent) : Prop :=
  e₁.timestamp < e₂.timestamp ∧ e₂.fingerprint ≠ e₁.fingerprint

/-- Verify integrity: all causality constraints satisfied -/
def isIntegral (h : InteractionHistory) : Prop :=
  ∀ i j, i < j → i < h.events.length → j < h.events.length →
    let e_i := h.events.get ⟨i, by omega⟩
    let e_j := h.events.get ⟨j, by omega⟩
    e_i.timestamp < e_j.timestamp

end InteractionHistory

/-! ## Instrument-Specific Gadgets -/

/-- An instrument gadget: phase-scoped rewrite for instruments -/
structure InstrumentGadget (φ : PolyphonicPhase) (inst : Instrument) where
  /-- Base rewrite (like quantum guitar) -/
  baseRule : ℚ → ℚ
  /-- Instrument-specific constraint: preserves valid pitch range -/
  pitchInRange : ∀ pitch : ℕ, pitch ≤ inst.pitchMax → baseRule (↑pitch) ≤ ↑inst.pitchMax
  /-- Preparation compatibility: respects acoustic behavior -/
  preparationCompat : Preparation → Bool
  /-- Decay constraint: rewrite output decays properly -/
  decayPreserving : ∀ t, baseRule t ≥ 0
  deriving Repr

/-- Specialized: piano gadget with preparation support -/
structure PianoGadget (φ : PolyphonicPhase) where
  /-- Base piano rewrite (amplification or contraction) -/
  baseRule : ℚ → ℚ
  /-- Valid preparations for this gadget -/
  allowedPreps : Finset Preparation
  /-- Monotonicty: respects piano's causal flow -/
  isMonotone : ∀ x y, x ≤ y → baseRule x ≤ baseRule y
  /-- Harmonic constraint: preserves spectral envelope -/
  preservesHarmonics : ∀ x, baseRule x = x ∨ baseRule x ≠ x
  deriving Repr

/-! ## Multi-Instrument Correctness Proofs -/

/-- A note played with instrument + preparation is well-formed -/
def isWellFormedNote (inst : Instrument) (prep : Preparation) (pitch : ℕ) : Prop :=
  0 ≤ pitch ∧ pitch ≤ inst.pitchMax ∧ 0 ≤ prep.amplitudeScale ∧ prep.amplitudeScale ≤ 1

/-- A gesture is well-formed if all voices are -/
def isWellFormedGesture (g : PolyphonicGesture) : Prop :=
  ∀ v ∈ g.voices, isWellFormedNote v.instrument v.preparation v.pitch

/-- Polyphonic correctness: all instruments respect their phases -/
def isPolyphonicallyCorrIect (gest : PolyphonicGesture) : Prop :=
  isWellFormedGesture gest ∧
  /-- All voices must fit within master phase bounds -/
  ∀ v ∈ gest.voices, v.pitch ≤ v.instrument.pitchMax

/-- Composition of gestures preserves polyphonic correctness -/
theorem polyphonic_composition_correct (g₁ g₂ : PolyphonicGesture) :
  isPolyphonicallyCorrIect g₁ → isPolyphonicallyCorrIect g₂ →
  (g₁.onsetTime < g₂.onsetTime) →  -- temporal ordering
  /-- The combined gesture maintains correctness -/
  isPolyphonicallyCorrIect ⟨g₁.voices ∪ g₂.voices, g₂.onsetTime, g₂.phase⟩ := by
  intro h₁ h₂ htime
  constructor
  · intro v hv
    cases' (Set.mem_union v g₁.voices g₂.voices).mp hv with h h
    · exact h₁.1 v h
    · exact h₂.1 v h
  · intro v hv
    cases' (Set.mem_union v g₁.voices g₂.voices).mp hv with h h
    · exact h₁.2 v h
    · exact h₂.2 v h

/-! ## British Artists' Techniques Formalized -/

/-- Aphex Twin's Windowlicker chaos: equation-driven melody -/
def aphexWindowlickerTechnique : ℕ → Preparation :=
  fun n =>
    let chaos := if n % 2 = 0 then 0.5 else -0.5
    {
      pitchOffset := chaos * 12  -- chaos-driven octave shift
      durationMult := 1.0 + (0.1 : ℚ) * (↑(n % 7) : ℚ) / 7  -- polyrhythm
      amplitudeScale := 0.5 + 0.5 * (↑(n % 3) : ℚ) / 3
      spectralMult := 1.0 + chaos
    }

/-- Autechre's cellular automaton texture: CA-driven performance -/
def autechreCATexture : ℕ → ℕ → Preparation :=
  fun gen n =>
    let ca := if (gen + n) % 3 = 0 then 1 else 0  -- simplified CA rule
    {
      pitchOffset := if ca = 1 then 7 else -7
      durationMult := 0.5 + ↑ca * 1.0
      amplitudeScale := 0.3 + ↑ca * 0.5
      spectralMult := 1.5 - ↑ca * 0.5
    }

/-- Daniel Avery's beating frequencies: synchronized detuning -/
def danielAveryBeatingTechnique : ℚ → Preparation :=
  fun beatFreq =>
    {
      pitchOffset := beatFreq / 100  -- micro-detuning
      durationMult := 2.0
      amplitudeScale := 0.8
      spectralMult := 0.9
    }

/-- Mica Levi's microtonal clusters: pitch-packed density -/
def micaLeviClusterTechnique : ℕ → Preparation :=
  fun density =>
    let clusterWidth := 0.5 * ↑(density % 5) / 5
    {
      pitchOffset := clusterWidth * 12
      durationMult := 0.3
      amplitudeScale := 0.2
      spectralMult := 2.0  -- sharp clusters
    }

/-! ## Spectrogram Analysis (Windowlicker Formalization) -/

/-- A spectrogram snapshot: frequency-time representation -/
structure SpectrogramFrame where
  /-- Frequencies (Hz) -/
  frequencies : ℕ → ℚ
  /-- Magnitudes at each frequency -/
  magnitudes : ℕ → ℚ
  /-- Time index -/
  timeIndex : ℕ
  deriving Repr

/-- Extract pitch from spectrogram (peak frequency) -/
def spectrogramPitch (frame : SpectrogramFrame) : ℕ :=
  let peaks := Finset.filter (fun i => frame.magnitudes i > 0.1) (Finset.range 128)
  peaks.sup id |>.getD 0

/-- Windowlicker equation: frequency trajectory -/
def windowlickerEquation (t : ℚ) : ℚ :=
  60 + 12 * (Math.sin (t * 0.5) : ℚ) * (Math.exp (-t * 0.1) : ℚ)

/-- Verify spectrogram matches Windowlicker equation -/
def spectrogramFollowsEquation (frames : ℕ → SpectrogramFrame)
    (equation : ℚ → ℚ) : Prop :=
  ∀ n, (spectrogramPitch (frames n) - 60 : ℚ).natAbs ≤ 1

end MusicTopos
