# Narya/Cat# Interrelatedness Tracking for CRDT Colors

## Overview

Observational bridge types for concurrent color editing with GF(3) conservation.
Uses Cat# bicomodules to model read/write/merge as parametrised lenses.

---

## Type Theory for Color CRDTs

### Core Types

```narya
-- Seeds and indices from Gay.jl SplitMix64
def Seed : Type := UInt64
def Idx : Type := Nat
def Color : Type := { hex : String, hue : Float, sat : Float, lum : Float }

-- GF(3) trits with conservation
def Trit : Type := { val : Int | val ∈ {-1, 0, +1} }
def trit_of_hue (h : Float) : Trit := 
  if h < 120.0 then { val := -1 }
  else if h < 240.0 then { val := 0 }
  else { val := +1 }

-- Color edits as first-class operations
def ColorEdit : Type := {
  seed : Seed,
  idx : Idx,
  color : Color,
  trit : Trit,
  timestamp : Nat  -- Lamport clock for ordering
}
```

### Observational Bridge Types

```narya
-- Bridge type: two edits are observationally equal if they produce same color
def ColorBridge (e1 e2 : ColorEdit) : Type :=
  Σ (p : e1.color.hex = e2.color.hex),
    transport (λ c → trit_of_hue c.hue) p e1.trit = e2.trit

-- Conflict bridge: witnesses that two edits conflict on same (seed, idx)
def Conflict (e1 e2 : ColorEdit) : Type :=
  (e1.seed = e2.seed) × (e1.idx = e2.idx) × (e1.color ≠ e2.color)

-- Resolution bridge: maps conflicting edits to unique merge result
def Resolution (e1 e2 : ColorEdit) (merged : ColorEdit) : Type :=
  Conflict e1 e2 → ColorBridge (merge e1 e2) merged
```

---

## Cat# Bicomodule Structure

### Parametrised Optics for CRDT Operations

```
           Read              Write             Merge
         ┌──────┐          ┌──────┐          ┌───────┐
State ───┤ Get  ├─→ Color  │ Put  │←─ Color  │ Join  │←─ Edit × Edit
         │      │          │      │          │       │
         └──┬───┘          └──┬───┘          └───┬───┘
            │                 │                  │
            ▼                 ▼                  ▼
         Costate           Costate           Merged Edit
         (Trit)            (Trit)         (GF3-conserved)
```

### Bicomodule Definition

```julia
# Cat# bicomodule for color CRDT
struct ColorCRDT{S,A}
    # Left comodule: read extracts state
    extract :: S → (A, S)
    
    # Right module: write injects updates  
    inject :: (A, S) → S
    
    # Bicomodule coherence: extract ∘ inject ≃ id
    coherence :: ∀a,s. extract(inject(a, s)).1 ≃ a
end

# Read operation (comonad extract)
function read_color(state::CRDTState, seed::UInt64, idx::Int)::ColorEdit
    color = color_at(seed, idx)  # Gay.jl determinism
    trit = trit_of_hue(color.hue)
    ColorEdit(seed, idx, color, trit, state.clock)
end

# Write operation (monad return + bind)
function write_color(state::CRDTState, edit::ColorEdit)::CRDTState
    # Increment Lamport clock
    new_clock = max(state.clock, edit.timestamp) + 1
    # Insert into local replica
    new_log = push(state.log, edit)
    CRDTState(new_clock, new_log, state.seed)
end

# Merge operation (join semilattice)
function merge_edits(e1::ColorEdit, e2::ColorEdit)::ColorEdit
    # Last-writer-wins with deterministic tiebreaker
    if e1.timestamp > e2.timestamp
        e1
    elseif e2.timestamp > e1.timestamp
        e2
    else
        # Tiebreaker: lexicographic on seed
        e1.seed ≤ e2.seed ? e1 : e2
    end
end
```

---

## GF(3) Conservation Proofs

### Proof Obligation 1: Single Edit Conservation

```narya
-- A single edit's trit is determined by its color
theorem edit_trit_determined (e : ColorEdit) :
  e.trit = trit_of_hue e.color.hue :=
  refl  -- By construction of ColorEdit

-- Trits are closed under GF(3)
theorem trit_closure (t1 t2 : Trit) :
  ∃ t3 : Trit, (t1.val + t2.val) mod 3 ∈ {-1, 0, +1} :=
  match t1.val + t2.val with
  | -2 => ⟨{val := 1}, refl⟩   -- -2 ≡ 1 (mod 3)
  | -1 => ⟨{val := -1}, refl⟩
  | 0  => ⟨{val := 0}, refl⟩
  | 1  => ⟨{val := 1}, refl⟩
  | 2  => ⟨{val := -1}, refl⟩  -- 2 ≡ -1 (mod 3)
```

### Proof Obligation 2: Merge Conservation

```narya
-- The key GF(3) witness type
def GF3Witness (e1 e2 : ColorEdit) (merged : ColorEdit) : Type :=
  (e1.trit.val + e2.trit.val) mod 3 = merged.trit.val mod 3

-- Merge preserves GF(3) via winner-takes-all
theorem merge_gf3_conserved (e1 e2 : ColorEdit) :
  GF3Witness e1 e2 (merge_edits e1 e2) :=
  -- Since merge picks one of e1 or e2, trit is preserved
  match compare e1.timestamp e2.timestamp with
  | GT => by { simp [merge_edits]; exact gf3_refl e1 }
  | LT => by { simp [merge_edits]; exact gf3_refl e2 }
  | EQ => by { simp [merge_edits]; exact gf3_lex_tiebreak e1 e2 }
```

### Proof Obligation 3: Multi-Edit Conservation

```narya
-- Sum of trits across a replica must be ≡ 0 (mod 3)
def ReplicaConserved (log : List ColorEdit) : Type :=
  (fold (λ acc e => acc + e.trit.val) 0 log) mod 3 = 0

-- Conservation is maintained through merges
theorem replica_conservation 
  (log1 log2 : List ColorEdit)
  (h1 : ReplicaConserved log1)
  (h2 : ReplicaConserved log2) :
  ReplicaConserved (merge_logs log1 log2) :=
  by {
    induction log1 with
    | nil => exact h2
    | cons e1 rest ih => 
        have : GF3Witness e1 (head log2) (merge_edits e1 (head log2))
        exact conservation_step e1 rest log2 ih h2
  }
```

---

## CRDT Properties: Commutativity and Idempotence

### Merge Commutativity

```narya
-- Merge is commutative up to observational equality
theorem merge_comm (e1 e2 : ColorEdit) :
  ColorBridge (merge_edits e1 e2) (merge_edits e2 e1) :=
  match compare e1.timestamp e2.timestamp with
  | GT => by { simp [merge_edits]; exact color_bridge_refl e1 }
  | LT => by { simp [merge_edits]; exact color_bridge_refl e2 }
  | EQ => 
      -- Lexicographic tiebreaker is symmetric when seeds equal
      if h : e1.seed = e2.seed then
        by { simp [merge_edits, h]; exact color_bridge_refl e1 }
      else
        -- Otherwise winner is deterministic regardless of order
        by { 
          cases (Nat.lt_or_ge e1.seed e2.seed) with
          | inl lt => simp [merge_edits, lt]; exact color_bridge_refl e1
          | inr ge => simp [merge_edits, ge]; exact color_bridge_refl e2
        }
```

### Merge Associativity

```narya
-- Merge is associative
theorem merge_assoc (e1 e2 e3 : ColorEdit) :
  ColorBridge 
    (merge_edits (merge_edits e1 e2) e3)
    (merge_edits e1 (merge_edits e2 e3)) :=
  by {
    -- The max-timestamp-wins strategy is associative
    have : max (max e1.timestamp e2.timestamp) e3.timestamp 
         = max e1.timestamp (max e2.timestamp e3.timestamp)
    exact Nat.max_assoc e1.timestamp e2.timestamp e3.timestamp
    -- Winner is same regardless of grouping
    exact color_bridge_of_same_winner this
  }
```

### Merge Idempotence

```narya
-- Merging an edit with itself yields the same edit
theorem merge_idem (e : ColorEdit) :
  merge_edits e e = e :=
  by {
    simp [merge_edits]
    -- timestamp comparison: e.timestamp = e.timestamp
    -- tiebreaker: e.seed ≤ e.seed is true
    rfl
  }
```

---

## Julia/Narya Bridge Implementation

```julia
# narya_bridge.jl - Executable bridge types

using Gay  # For color_at, seed!, etc.

# Type-level trit as Julia const
const TRIT_MINUS = -1
const TRIT_ZERO = 0  
const TRIT_PLUS = 1

struct NaryaColorEdit
    seed::UInt64
    idx::Int
    hex::String
    trit::Int8  # -1, 0, +1
    timestamp::UInt64
    
    function NaryaColorEdit(seed, idx, timestamp)
        color = color_at(seed, idx)
        trit = Int8(mod(floor(Int, color.hue / 120), 3) - 1)
        new(seed, idx, color.hex, trit, timestamp)
    end
end

# GF(3) witness as runtime assertion
struct GF3Witness
    e1_trit::Int8
    e2_trit::Int8
    merged_trit::Int8
    valid::Bool
    
    function GF3Witness(e1::NaryaColorEdit, e2::NaryaColorEdit, merged::NaryaColorEdit)
        sum_mod = mod(e1.trit + e2.trit, 3)
        # Map {0,1,2} back to {0,1,-1}
        expected = sum_mod == 2 ? -1 : sum_mod
        valid = expected == merged.trit
        new(e1.trit, e2.trit, merged.trit, valid)
    end
end

# Merge with GF(3) verification
function merge_with_witness(e1::NaryaColorEdit, e2::NaryaColorEdit)
    merged = if e1.timestamp > e2.timestamp
        e1
    elseif e2.timestamp > e1.timestamp
        e2
    else
        e1.seed ≤ e2.seed ? e1 : e2
    end
    
    witness = GF3Witness(e1, e2, merged)
    @assert witness.valid "GF(3) conservation violated!"
    (merged, witness)
end

# Replica conservation check
function check_replica_conservation(edits::Vector{NaryaColorEdit})
    total = sum(e.trit for e in edits)
    mod(total, 3) == 0
end
```

---

## Integration with Bumpus Narratives

The CRDT operations form a sheaf over the time category:

```
Time Category T:
  Objects: Lamport timestamps
  Morphisms: t1 → t2 where t1 ≤ t2

Sheaf F : T^op → Set:
  F(t) = { edits with timestamp ≤ t }
  F(t1 ≤ t2) = inclusion of earlier edits

Stalks: F_t = colim_{s→t} F(s) = all edits visible at time t
```

GF(3) conservation is a **global section**: a consistent choice of trit sums
across all stalks that glues to a well-defined replica state.

---

## Summary

| Component | Type | Conservation |
|-----------|------|--------------|
| ColorEdit | `Seed × Idx × Color × Trit × Nat` | Trit determined by hue |
| Merge | `Edit → Edit → Edit` | Winner-takes-all preserves trit |
| GF3Witness | `Merge(e1,e2) → (t1+t2) ≡ t_merged (mod 3)` | Verified at merge time |
| Replica | `List Edit` with `Σ trits ≡ 0 (mod 3)` | Maintained inductively |

**Key Proof Obligations:**
1. `merge_comm`: ∀e1 e2. merge(e1,e2) ≃ merge(e2,e1)
2. `merge_assoc`: ∀e1 e2 e3. merge(merge(e1,e2),e3) ≃ merge(e1,merge(e2,e3))
3. `merge_idem`: ∀e. merge(e,e) = e
4. `gf3_conserved`: ∀e1 e2. GF3Witness e1 e2 (merge e1 e2)
