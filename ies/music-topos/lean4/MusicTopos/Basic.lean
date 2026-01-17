/-
  MusicTopos.Basic

  Core definitions for the MusicTopos system.
  GF(3)-conserved categorical music theory.
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Defs

namespace MusicTopos

/-! ## Core Types -/

/-- LCH Color representation (Lightness, Chroma, Hue) using rationals -/
structure LCHColor where
  L : Int  -- Lightness [0, 100] scaled
  C : Int  -- Chroma [0, ∞) scaled
  H : Int  -- Hue [0, 360) scaled
  deriving DecidableEq, Repr

/-- Harmonic function (tonic, subdominant, dominant) -/
inductive HarmonicFunc : Type where
  | tonic : HarmonicFunc
  | subdominant : HarmonicFunc
  | dominant : HarmonicFunc
  deriving DecidableEq, Repr

/-- Network weights for preference learning -/
structure NetworkWeights where
  weights : List Int
  deriving DecidableEq, Repr

/-! ## Color to Function Mapping -/

/-- Map hue to harmonic function -/
def hue_to_function (hue : Int) : HarmonicFunc :=
  if hue < 90 then HarmonicFunc.tonic
  else if hue < 210 then HarmonicFunc.subdominant
  else if hue < 330 then HarmonicFunc.dominant
  else HarmonicFunc.tonic

/-- Map color to harmonic function -/
def color_to_function (c : LCHColor) : HarmonicFunc :=
  hue_to_function c.H

/-! ## Möbius Inversion -/

/-- Möbius function on GF(3) -/
def moebius3 : ZMod 3 := -1

/-- Möbius merge of three elements -/
def moebius_merge {G : Type*} [AddCommGroup G]
    (states : Fin 3 → G) : G :=
  states 0 + states 1 + states 2

end MusicTopos
