/-
  IBCCollision.lean — Formal proofs of IBC denomination collision inevitability
  and authenticated-denom injectivity as a mitigation.

  Security disclosure: IBC `transfer/channel-N/denom` paths collide
  when distinct chains share channel IDs. Trit-augmented authentication
  restores injectivity while preserving GF(3) #-conservation.
-/

import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic

-- Inline GF(3) definitions from HashTheory (avoids depending on broken upstream)
abbrev GF3 := ZMod 3

namespace Trit
  def plus : GF3 := 1
  def ergodic : GF3 := 0
  def minus : GF3 := 2
end Trit

def hashConserved (trits : List GF3) : Prop := trits.sum = 0

theorem hash_concat_closed (xs ys : List GF3) :
    hashConserved xs → hashConserved ys → hashConserved (xs ++ ys) := by
  simp [hashConserved, List.sum_append]
  intro hx hy
  rw [hx, hy]
  ring

-- ============================================================================
-- SECTION I: DOMAIN MODELING
-- ============================================================================

/-- A chain identifier (opaque). -/
abbrev Chain := String

/-- A channel identifier (finite namespace). -/
abbrev ChannelId := String

/-- The IBC denomination path: `transfer/channel-N/denom`.
    Two chains that happen to use the same channel-id produce
    the same path string — this is the vulnerability. -/
def denomPath (_chain : Chain) (chan : ChannelId) (baseDenom : String) : String :=
  "transfer/" ++ chan ++ "/" ++ baseDenom

-- ============================================================================
-- SECTION II: PIGEONHOLE — COLLISION INEVITABILITY
-- ============================================================================

/-- When there are strictly more chains than available channel IDs,
    some two distinct chains must map to the same channel ID.
    This is the finite pigeonhole principle from Mathlib. -/
theorem pigeonhole_collision_inevitable
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β)
    (h : Fintype.card β < Fintype.card α) :
    ∃ a₁ a₂ : α, a₁ ≠ a₂ ∧ f a₁ = f a₂ :=
  Fintype.exists_ne_map_eq_of_card_lt f h

-- ============================================================================
-- SECTION III: DENOM PATH NON-INJECTIVITY
-- ============================================================================

/-- If two distinct chains use the same channel-id and the same base denom,
    their IBC denom paths are identical. This is immediate from the
    definition — `denomPath` ignores the chain argument. -/
theorem denomPath_not_injective
    (c₁ c₂ : Chain) (chan : ChannelId) (baseDenom : String)
    (_hne : c₁ ≠ c₂) :
    denomPath c₁ chan baseDenom = denomPath c₂ chan baseDenom := by
  simp [denomPath]

-- ============================================================================
-- SECTION IV: AUTHENTICATED DENOM — INJECTIVITY RESTORED
-- ============================================================================

/-- An authenticated denomination bundles the denom path with
    a chain fingerprint (e.g. chain-id hash, genesis hash). -/
structure AuthDenom where
  denom : String
  chain_fingerprint : String
  deriving DecidableEq, Repr

/-- Build an AuthDenom from chain info. -/
def mkAuthDenom (chain : Chain) (chan : ChannelId) (baseDenom : String)
    (fingerprint : Chain → String) : AuthDenom :=
  { denom := denomPath chain chan baseDenom
    chain_fingerprint := fingerprint chain }

/-- When the fingerprint function is injective (i.e. it distinguishes
    chains), `mkAuthDenom` is injective in the chain argument —
    even when the channel-id and base denom coincide. -/
theorem authDenom_injective
    (chan : ChannelId) (baseDenom : String)
    (fingerprint : Chain → String)
    (hfp : Function.Injective fingerprint) :
    Function.Injective (fun chain => mkAuthDenom chain chan baseDenom fingerprint) := by
  intro c₁ c₂ heq
  simp [mkAuthDenom, AuthDenom.mk.injEq] at heq
  exact hfp heq.2

-- ============================================================================
-- SECTION V: GF(3) CONSERVATION — TRIT-AUGMENTED AUTH
-- ============================================================================

/-- A trit-graded authentication triple:
    (denom_path : PLUS, channel_proof : ERGODIC, chain_fingerprint : MINUS).
    This mirrors the bicomodule c ↔ m ↔ d stack. -/
structure TritAuthDenom where
  denom_path       : String
  channel_proof    : String
  chain_fingerprint : String
  /-- GF(3) grades -/
  denom_trit       : GF3 := Trit.plus
  proof_trit       : GF3 := Trit.ergodic
  fingerprint_trit : GF3 := Trit.minus

/-- The canonical trit triple (PLUS, ERGODIC, MINUS) is #-conserved. -/
theorem tritAuth_conserved :
    hashConserved [Trit.plus, Trit.ergodic, Trit.minus] := by
  simp [hashConserved, Trit.plus, Trit.ergodic, Trit.minus]
  decide

/-- Connecting to HashTheory: the trit assignment forms a valid Bicomodule grading.
    The c(ontrol) = denom_path, m(iddleware) = channel_proof, d(ata) = fingerprint
    assignment preserves the canonical conservation law. -/
theorem tritAuth_bicomodule_conserved :
    Trit.plus + Trit.ergodic + Trit.minus = (0 : GF3) := by
  simp [Trit.plus, Trit.ergodic, Trit.minus]
  decide

/-- #-conservation is preserved when we concatenate two trit triples. -/
theorem tritAuth_concat_conserved :
    hashConserved ([Trit.plus, Trit.ergodic, Trit.minus] ++
                   [Trit.plus, Trit.ergodic, Trit.minus]) := by
  exact hash_concat_closed _ _ tritAuth_conserved tritAuth_conserved
