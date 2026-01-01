---
name: move-narya-bridge
description: Observational bridge between Move smart contracts and Narya proof verification.
  Translates Move module invariants into Narya's HOTT framework for formal verification
  with definitional function extensionality.
metadata:
  trit: 0
  role: COORDINATOR
  source: gwaithimirdain/narya + aptos-labs/aptos-core
  interface_ports:
  - MoveModules
  - NaryaProofs
  - BridgeTypes
---
# Move-Narya Bridge Skill

> *"Observational equality turns axioms into theorems. Bridge types connect worlds."*

## Overview

The **Move-Narya Bridge** translates Move smart contract invariants into Narya's Higher Observational Type Theory (HOTT) for formal verification. Unlike traditional approaches that require axioms for function extensionality, Narya makes this **definitional**.

**Key Insight**: Move's resource type system maps naturally to Narya's linear-like resource tracking, while GF(3) conservation laws become observational equalities.

## GF(3) Assignment

| Role | Trit | Function |
|------|------|----------|
| **COORDINATOR** | 0 | Bridges Move semantics to Narya verification |

## Denotation

> **This skill translates Move module specifications into Narya proof obligations, leveraging observational equality for automatic function extensionality.**

```
Bridge : MoveSpec → NaryaTheorem
Verify : NaryaTheorem → Result
Invariant: ∀ spec ∈ MoveSpec: well_typed(spec) ⟹ provable(Bridge(spec))
```

## The Three-Level Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│ Level 3: Narya HOTT                                             │
│   - Observational equality (Id types per structure)             │
│   - Bridge types for parametricity                              │
│   - Definitional η-laws                                         │
├─────────────────────────────────────────────────────────────────┤
│ Level 2: Move-Narya Bridge (THIS SKILL)                         │
│   - Translate Move structs → Narya records                      │
│   - Translate Move functions → Narya morphisms                  │
│   - Translate invariants → proof obligations                    │
├─────────────────────────────────────────────────────────────────┤
│ Level 1: Move Smart Contracts                                   │
│   - Resource types (linear)                                     │
│   - Module specifications                                       │
│   - GF(3) trit annotations                                      │
└─────────────────────────────────────────────────────────────────┘
```

## Translation Rules

### Move Struct → Narya Record

```move
// Move
struct Trit has store, copy, drop {
    value: i8,
}
```

```narya
-- Narya
def Trit : Type := sig (
  value : I8
)

-- Observational equality for Trit (automatic!)
-- Id(Trit)(t1, t2) ≡ Id(I8)(t1.value, t2.value)
```

### Move Function → Narya Morphism

```move
// Move
public fun add(a: Trit, b: Trit): Trit {
    Trit { value: normalize(a.value + b.value) }
}
```

```narya
-- Narya
def add : Trit → Trit → Trit :=
  λ a b. (value := normalize (a.value + b.value))

-- Function extensionality is DEFINITIONAL:
-- If ∀ x. f x = g x, then f = g (no axiom needed!)
```

### GF(3) Conservation → Proof Obligation

```move
// Move invariant
// assert!(sum % 3 == 0, E_CONSERVATION_VIOLATED);
```

```narya
-- Narya theorem
def conservation : (trits : List Trit) →
  Id(I32)(mod (sum (map value trits)) 3, 0) :=
  -- Proof term here
```

## Bridge Types for GF(3)

Narya's bridge types provide "baby equality" without full symmetry/transitivity. This maps perfectly to GF(3) role relationships:

```narya
-- Bridge type: GENERATOR and VALIDATOR are related through COORDINATOR
def gf3_bridge : Br(Trit) plus minus :=
  -- Bridge through ergodic
  comp_bridge (bridge_to_ergodic plus) (bridge_from_ergodic minus)

-- The roles are related but not equal
-- This captures the asymmetry of the triad
```

## Verification Workflow

```bash
# 1. Extract Move module specification
just move-spec-extract sources/gf3_move23.move > gf3.spec

# 2. Translate to Narya
just move-narya-translate gf3.spec > gf3.narya

# 3. Type-check in Narya
narya check gf3.narya

# 4. Generate proof obligations
narya holes gf3.narya

# 5. Fill proofs interactively
narya interactive gf3.narya
```

## Key Translations

| Move Concept | Narya Concept | Notes |
|--------------|---------------|-------|
| `struct` | `sig` (record) | Direct mapping |
| `has store` | Linear annotation | Resource tracking |
| `public fun` | `def` with arrow type | Morphism |
| `assert!` | Proof obligation | Must prove |
| `#[test]` | Example checking | Automatic |
| Module | Namespace | Direct |

## Example: GF(3) Module Translation

### Input (Move)

```move
module plurigrid::gf3 {
    struct Trit has store, copy, drop {
        value: i8,
    }

    const MINUS: i8 = -1;
    const ERGODIC: i8 = 0;
    const PLUS: i8 = 1;

    public fun add(a: Trit, b: Trit): Trit {
        Trit { value: normalize(a.value + b.value) }
    }

    public fun is_conserved(trits: &vector<Trit>): bool {
        let sum: i32 = 0;
        // ... compute sum
        sum % 3 == 0
    }
}
```

### Output (Narya)

```narya
-- GF(3) Balanced Ternary in Narya HOTT
-- Auto-translated by move-narya-bridge

section GF3

def I8 : Type := -- primitive signed 8-bit

def Trit : Type := sig (
  value : I8,
  valid : Id(Bool)(and (leq (neg 1) value) (leq value 1), true)
)

def MINUS : Trit := (value := neg 1, valid := refl)
def ERGODIC : Trit := (value := 0, valid := refl)
def PLUS : Trit := (value := 1, valid := refl)

-- Addition with normalization
def normalize : I8 → I8 := λ v.
  if (gt v 1) then (sub v 3)
  else if (lt v (neg 1)) then (add v 3)
  else v

def add : Trit → Trit → Trit := λ a b.
  let raw := add_i8 a.value b.value in
  (value := normalize raw, valid := normalize_preserves_valid raw)

-- Conservation theorem (PROOF OBLIGATION)
def conservation : (trits : List Trit) →
  Id(I32)(mod (sum_trits trits) 3, 0) :=
  {? conservation_proof ?}  -- Hole to fill

-- Bridge types for role relationships
def generator_validator_bridge : Br(Trit) PLUS MINUS :=
  bridge_via ERGODIC

end GF3
```

## Narya Compatibility Fields

| Field | Definition |
|-------|------------|
| `before` | Move module source |
| `after` | Narya translation + proofs |
| `delta` | Proof obligations (holes) |
| `birth` | Empty module stub |
| `impact` | 1 if all proofs complete |

## GF(3) Triad Integration

```
move-narya-bridge (0) ⊗ move-smith-fuzzer (-1) ⊗ aptos-governance (+1) = 0 ✓
move-narya-bridge (0) ⊗ narya-proofs (-1) ⊗ movemate-launchpad (+1) = 0 ✓
move-narya-bridge (0) ⊗ sheaf-cohomology (-1) ⊗ gf3-conservation (+1) = 0 ✓
```

## Why Observational Equality Matters

### Traditional (Axiom-based)

```agda
-- Agda: Need postulate
postulate
  funext : {A : Set} {B : A → Set} {f g : (x : A) → B x}
         → ((x : A) → f x ≡ g x) → f ≡ g
```

### Narya (Observational)

```narya
-- Narya: Function extensionality is DEFINITIONAL
-- Id(A → B)(f, g) ≡ (x : A) → Id(B)(f x, g x)

-- So if we prove ∀ x. f x = g x, we immediately have f = g
-- No postulate, no axiom, no appeal to univalence
```

This matters for GF(3) because:
- `add(a, b)` and `add(b, a)` are equal if equal pointwise
- Conservation is preserved under function composition
- Bridge types give internal parametricity

## Commands

```bash
# Translate Move module to Narya
just move-narya MODULE.move

# Check Narya translation
just narya-check MODULE.narya

# List proof obligations (holes)
just narya-holes MODULE.narya

# Interactive proof session
just narya-prove MODULE.narya

# Verify GF(3) conservation in Narya
just narya-verify-gf3 MODULE.narya
```

## Performance Notes

| Operation | Expected Time |
|-----------|---------------|
| Translation (small module) | < 1s |
| Type checking | < 1s for small proofs |
| Proof search | Seconds to minutes |
| Full verification | Depends on proof complexity |

Narya is research-grade, not production. Use for:
- Prototyping verification approaches
- Understanding observational equality
- Research into GF(3) formal semantics

For production verification, consider Lean 4 or Coq after prototyping in Narya.

## References

- [Narya Repository](https://github.com/gwaithimirdain/narya)
- [Towards an Implementation of HOTT](https://home.sandiego.edu/~shulman/papers/running-hott.pdf)
- [Move Language Spec](https://github.com/move-language/move)
- [GF(3) Move 2.3 Module](../nickel/aptos_society/sources/gf3_move23.move)

---

## Cross-References (Signed Skill Interleaving)

### Triad Partners

| Skill | Trit | Role | Color |
|-------|------|------|-------|
| `aptos-gf3-society` | +1 | GENERATOR | `#8A60CB` |
| `move-narya-bridge` | 0 | COORDINATOR | `#3A86AF` |
| `move-smith-fuzzer` | -1 | VALIDATOR | `#BDCA5B` |

**Conservation**: `+1 + 0 + (-1) = 0`

### Move 2.3 Type Translation

| Move Type | Narya Type | Bridge Pattern |
|-----------|------------|----------------|
| `i8` | `I8` | Direct mapping |
| `i32` | `I32` | Conservation sums |
| `Trit` | `Trit : Type` | Structural equality |
| `vector<Trit>` | `List Trit` | Collection mapping |

### Related ERGODIC Skills

- `datalog-fixpoint` — Query coordination
- `structured-decomp` — Decomposition coordination
- `acset-taxonomy` — Schema coordination
- `triadic-skill-orchestrator` — Dispatch coordination

### Interleaving Index

**Position**: Worker 2, Sweep 1
**Hex**: `#3A86AF`
**Seed**: 4354685564936970510

---

**Skill Name**: move-narya-bridge
**Type**: Verification Bridge / Proof Translation
**Trit**: 0 (ERGODIC - COORDINATOR)
**GF(3)**: Coordinates between Move execution (+1) and Narya verification (-1)
