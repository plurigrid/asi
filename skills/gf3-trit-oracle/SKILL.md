---
name: gf3-trit-oracle
<<<<<<< HEAD
description: The fundamental GF(3) trit oracle. Maps any skill, operation, agent, or value to exactly one of {-1, 0, +1} with formal pre/post-conditions and a canonical CellValue{Nothing, Value, Contradiction} lattice for partial information accumulation. This is the atomic oracle that all other GF(3) machinery depends on.
version: 1.0.0
trit: 0
role: ERGODIC
tags: [gf3, oracle, trit, formal, specification, propagator, cell-value]
deployed: 2026-02-19
=======
description: >
  The fundamental GF(3) trit oracle. Maps any skill, operation, agent, or value
  to exactly one of {-1, 0, +1} with CellValue{Nothing, Value, Contradiction} lattice.
  Triggers: classify trit, assign trit value, GF(3) classification, trit oracle,
  propagator cell value, partial information lattice.
>>>>>>> origin/main
---

# GF(3) Trit Oracle

## Formal Specification

### Type

```
<<<<<<< HEAD
TritOracle : X → Trit
Trit       = {-1, 0, +1} ⊂ ℤ/3ℤ

Invariant:  ∀ x₁, x₂, x₃ ∈ X valid-triad(x₁,x₂,x₃) →
            TritOracle(x₁) + TritOracle(x₂) + TritOracle(x₃) ≡ 0  (mod 3)
=======
TritOracle : X -> Trit
Trit       = {-1, 0, +1} subset Z/3Z

Invariant:  for all x1, x2, x3 in X valid-triad(x1,x2,x3) ->
            TritOracle(x1) + TritOracle(x2) + TritOracle(x3) = 0  (mod 3)
>>>>>>> origin/main
```

### Preconditions

<<<<<<< HEAD
1. `x` is a well-formed skill, operation, agent, or value in the ASI universe
2. `x` has a unique canonical identifier (skill name, CID, or hash)
3. The oracle has access to at least one of: (a) `skills.json` registry entry, (b) behavioral trace, (c) structural signature

### Postconditions

1. Returns exactly one value in `{-1, 0, +1}` — never `null`, never partial
2. Deterministic: same input → same output (no randomness)
=======
1. `x` is a well-formed skill, operation, agent, or value
2. `x` has a unique canonical identifier
3. The oracle has access to at least one of: (a) registry entry, (b) behavioral trace, (c) structural signature

### Postconditions

1. Returns exactly one value in `{-1, 0, +1}`
2. Deterministic: same input -> same output
>>>>>>> origin/main
3. Conservation: any trit triad produced by `build_triad` sums to 0 mod 3

### Failure mode

<<<<<<< HEAD
If the oracle cannot determine a trit (input unknown), it returns `CellValue.nothing` — NOT a guess. `CellValue.contradiction` is returned if two authoritative sources disagree.

---
=======
Returns `CellValue.nothing` if input unknown. Returns `CellValue.contradiction` if two authoritative sources disagree.
>>>>>>> origin/main

## The CellValue Lattice (from propagator.zig)

```zig
// Partial information lattice
// Ordering: nothing < value(-1|0|+1) < contradiction
pub fn CellValue(comptime T: type) type {
    return union(enum) {
<<<<<<< HEAD
        nothing,                              // oracle has no information yet
        value: T,                             // oracle has a definite answer
        contradiction: struct { a: T, b: T }, // two sources disagree
    };
}

// The ONLY merge operation
=======
        nothing,
        value: T,
        contradiction: struct { a: T, b: T },
    };
}

>>>>>>> origin/main
pub fn latticeMerge(existing: CellValue(Trit), incoming: CellValue(Trit)) CellValue(Trit) {
    return switch (existing) {
        .nothing      => incoming,
        .contradiction => existing,
        .value => |v| switch (incoming) {
            .nothing      => existing,
            .value => |w| if (v == w) existing
                          else .{ .contradiction = .{ .a = v, .b = w } },
            .contradiction => incoming,
        },
    };
}
```

<<<<<<< HEAD
This lattice is the **only** way trit values accumulate. No averaging, no weighted voting, no softmax. Either you know, or you don't.

---

=======
>>>>>>> origin/main
## Oracle Implementations (in order of authority)

### 1. Registry Oracle (highest authority)

```bash
# Requirement: skills.json entry exists with "trit" field
<<<<<<< HEAD
# Requirement: trit ∈ {-1, 0, 1} (integers, not strings)
# Postcondition: returns CellValue.value(trit_from_registry)

=======
>>>>>>> origin/main
jq -r --arg name "$SKILL_NAME" \
  '.skills[] | select(.name == $name) | .trit' \
  ~/i/asi/skills.json
# Output: -1 | 0 | 1
<<<<<<< HEAD
# If not found: returns CellValue.nothing (empty output)
=======
# If not found: CellValue.nothing
>>>>>>> origin/main
```

### 2. Structural Oracle

```python
<<<<<<< HEAD
# Requirement: skill has SKILL.md with role: field
# Precondition: role ∈ {VALIDATOR, ERGODIC, GENERATOR, BRIDGE}
# Postcondition: deterministic mapping to trit

ROLE_TO_TRIT = {
    "VALIDATOR": -1,   # verifies, constrains, reduces
    "ERGODIC":    0,   # mediates, balances, routes
    "BRIDGE":     0,   # connects (same as ERGODIC)
    "GENERATOR": +1,   # creates, composes, generates
}

def structural_oracle(skill_path: str) -> CellValue[int]:
=======
ROLE_TO_TRIT = {
    "VALIDATOR": -1,
    "ERGODIC":    0,
    "BRIDGE":     0,
    "GENERATOR": +1,
}

def structural_oracle(skill_path: str):
>>>>>>> origin/main
    frontmatter = parse_frontmatter(skill_path + "/SKILL.md")
    role = frontmatter.get("role")
    if role is None:
        return CellValue.nothing()
    trit = ROLE_TO_TRIT.get(role)
    if trit is None:
        return CellValue.nothing()
    return CellValue.value(trit)
```

### 3. Behavioral Oracle (Gemini)

Only invoked when registry and structural oracles return `CellValue.nothing`.

```bash
<<<<<<< HEAD
# Requirement: access to Gemini API (OAuth2 bearer token)
# Requirement: skill description text ≥ 50 characters
# Postcondition: response is EXACTLY one of "-1", "0", "+1"
# Fallback on malformed response: CellValue.nothing (NOT a guess)

=======
>>>>>>> origin/main
SKILL_DESC="$1"
TOKEN=$(gcloud auth print-access-token)
PROJECT=$(gcloud config get project 2>/dev/null)

RESPONSE=$(curl -s -X POST \
  "https://us-central1-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/us-central1/publishers/google/models/gemini-2.0-flash:generateContent" \
  -H "Authorization: Bearer ${TOKEN}" \
  -H "Content-Type: application/json" \
  -d "{
<<<<<<< HEAD
    \"contents\": [{\"role\": \"user\", \"parts\": [{\"text\": \"Classify this skill/operation as exactly one of: -1 (validates/constrains/reduces), 0 (mediates/routes/bridges), or +1 (creates/composes/generates). Respond with ONLY the number, nothing else. Skill: ${SKILL_DESC}\"}]}],
    \"generationConfig\": {\"temperature\": 0.0, \"maxOutputTokens\": 4}
  }" | jq -r '.candidates[0].content.parts[0].text' | tr -d '[:space:]')

# Strict validation
case "$RESPONSE" in
  "-1"|"0"|"1"|"+1") echo "${RESPONSE/+/}" ;;
  *) echo "nothing" ;;  # malformed → CellValue.nothing
=======
    \"contents\": [{\"role\": \"user\", \"parts\": [{\"text\": \"Classify this skill as exactly one of: -1 (validates/constrains), 0 (mediates/routes), or +1 (creates/composes). Respond with ONLY the number. Skill: ${SKILL_DESC}\"}]}],
    \"generationConfig\": {\"temperature\": 0.0, \"maxOutputTokens\": 4}
  }" | jq -r '.candidates[0].content.parts[0].text' | tr -d '[:space:]')

case "$RESPONSE" in
  "-1"|"0"|"1"|"+1") echo "${RESPONSE/+/}" ;;
  *) echo "nothing" ;;
>>>>>>> origin/main
esac
```

### 4. Propagator Network Oracle

<<<<<<< HEAD
When multiple sources provide trit evidence, accumulate via the lattice:

```python
def propagator_oracle(skill_name: str) -> CellValue[int]:
    """Accumulate trit evidence from all sources via latticeMerge."""
    cell = CellValue.nothing()

    # Source 1: registry
    cell = lattice_merge(cell, registry_oracle(skill_name))
    if cell.is_contradiction():
        return cell  # contradiction absorbs all

    # Source 2: structural
=======
```python
def propagator_oracle(skill_name: str):
    """Accumulate trit evidence from all sources via latticeMerge."""
    cell = CellValue.nothing()

    cell = lattice_merge(cell, registry_oracle(skill_name))
    if cell.is_contradiction():
        return cell

>>>>>>> origin/main
    cell = lattice_merge(cell, structural_oracle(skill_path(skill_name)))
    if cell.is_contradiction():
        return cell

<<<<<<< HEAD
    # Source 3: behavioral (only if still nothing)
=======
>>>>>>> origin/main
    if cell.is_nothing():
        cell = lattice_merge(cell, behavioral_oracle(skill_description(skill_name)))

    return cell
```

<<<<<<< HEAD
---

## Trit Arithmetic (GF(3))

```python
# GF(3) = ℤ/3ℤ with elements {-1, 0, +1} ≡ {2, 0, 1} mod 3

def gf3_add(a: int, b: int) -> int:
    """Add two trits in GF(3). Result ∈ {-1, 0, +1}."""
    raw = (a + b) % 3
    return raw if raw <= 1 else raw - 3  # map {2} → {-1}

def gf3_mul(a: int, b: int) -> int:
    """Multiply two trits in GF(3). Result ∈ {-1, 0, +1}."""
=======
## Trit Arithmetic (GF(3))

```python
def gf3_add(a: int, b: int) -> int:
    raw = (a + b) % 3
    return raw if raw <= 1 else raw - 3

def gf3_mul(a: int, b: int) -> int:
>>>>>>> origin/main
    raw = (a * b) % 3
    return raw if raw <= 1 else raw - 3

def is_valid_triad(t1: int, t2: int, t3: int) -> bool:
<<<<<<< HEAD
    """Conservation law: Σ trits ≡ 0 mod 3."""
=======
>>>>>>> origin/main
    return gf3_add(gf3_add(t1, t2), t3) == 0

def build_triad(t1: int, t2: int) -> int:
    """Given two trits, compute the unique third that conserves GF(3)."""
<<<<<<< HEAD
    return gf3_add(-(t1 + t2) % 3, 0)  # t3 = -(t1+t2) mod 3
```

---

## Oracle Composition

Two trit oracles compose **only** if the triad is valid:

```python
def compose_skills(s1: str, s2: str, s3: str) -> Optional[Composition]:
    """
    Compose three skills if and only if their trit triad is valid.

    Precondition:  all three trits are CellValue.value (not nothing/contradiction)
    Postcondition: iff is_valid_triad(t1, t2, t3) → Composition(s1, s2, s3)
                   else → None (composition refused)
    """
    t1 = propagator_oracle(s1)
    t2 = propagator_oracle(s2)
    t3 = propagator_oracle(s3)

    # Reject partial information
    if any(c.is_nothing() or c.is_contradiction() for c in [t1, t2, t3]):
        return None  # cannot compose without complete trit information

    # Enforce conservation law
    if not is_valid_triad(t1.value, t2.value, t3.value):
        return None  # trit conservation violated → composition refused

    return Composition(s1, s2, s3)
```

---

## Neurofeedback Trit Oracle (from propagator.zig)

The BCI-to-trit oracle is a concrete instance:

```zig
// Requirement: focus ∈ [0.0, 1.0] (EEG-derived focus score)
// Postcondition: trit ∈ {-1, 0, +1}, deterministic

fn neurofeedback_trit(focus: f32) Trit {
    return if (focus > 0.66) .plus          // high focus → Generator (+1)
    else if (focus < 0.33) .minus           // low focus  → Validator (-1)
    else .zero;                             // medium     → Coordinator (0)
}
// This is a SPECIFIC oracle. Threshold: 0.33, 0.66. No fuzz.
```

---

## What This Oracle Is NOT

- NOT a softmax over trit probabilities — trits are discrete, not continuous
- NOT a learnable parameter — trits are determined, not trained
- NOT a majority vote — the lattice uses identity or contradiction, never averaging
- NOT partial — a trit is either known (value) or unknown (nothing), never "0.7"
- NOT overridable — once `CellValue.contradiction`, it stays contradiction

---

## Related Skills

- `gf3-tripartite` — composition invariant checker
- `gf3-pr-verify` — pre-commit hook enforcing conservation
- `skill-validation-gf3` — validates skill registry entries
- `bisimulation-game` — behavioral equivalence oracle (uses trit as classification)
- `propagators` — Radul-Sussman propagator network (the CellValue lattice)
- `zig-syrup-propagator-interleave` — propagator.zig with neurofeedback_gate
- `balance-triad` (Gay.jl) — `is_valid_triad` in Julia
- `triad-interleave` — trit-conserving skill composition router
=======
    return gf3_add(-(t1 + t2) % 3, 0)
```

## Neurofeedback Trit Oracle

```zig
fn neurofeedback_trit(focus: f32) Trit {
    return if (focus > 0.66) .plus          // high focus -> Generator (+1)
    else if (focus < 0.33) .minus           // low focus  -> Validator (-1)
    else .zero;                             // medium     -> Coordinator (0)
}
```

## What This Oracle Is NOT

- NOT a softmax over probabilities -- trits are discrete
- NOT a learnable parameter -- trits are determined, not trained
- NOT a majority vote -- identity or contradiction, never averaging
- NOT partial -- a trit is known (value) or unknown (nothing), never "0.7"
- NOT overridable -- once `CellValue.contradiction`, it stays
>>>>>>> origin/main


## Para(Optic) atlas

Part of: `para-mensch-commons`.
