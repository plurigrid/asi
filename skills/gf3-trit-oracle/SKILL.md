---
name: gf3-trit-oracle
description: >
  The fundamental GF(3) trit oracle. Maps any skill, operation, agent, or value
  to exactly one of {-1, 0, +1} with CellValue{Nothing, Value, Contradiction} lattice.
  Triggers: classify trit, assign trit value, GF(3) classification, trit oracle,
  propagator cell value, partial information lattice.
---

# GF(3) Trit Oracle

## Formal Specification

### Type

```
TritOracle : X -> Trit
Trit       = {-1, 0, +1} subset Z/3Z

Invariant:  for all x1, x2, x3 in X valid-triad(x1,x2,x3) ->
            TritOracle(x1) + TritOracle(x2) + TritOracle(x3) = 0  (mod 3)
```

### Preconditions

1. `x` is a well-formed skill, operation, agent, or value
2. `x` has a unique canonical identifier
3. The oracle has access to at least one of: (a) registry entry, (b) behavioral trace, (c) structural signature

### Postconditions

1. Returns exactly one value in `{-1, 0, +1}`
2. Deterministic: same input -> same output
3. Conservation: any trit triad produced by `build_triad` sums to 0 mod 3

### Failure mode

Returns `CellValue.nothing` if input unknown. Returns `CellValue.contradiction` if two authoritative sources disagree.

## The CellValue Lattice (from propagator.zig)

```zig
// Partial information lattice
// Ordering: nothing < value(-1|0|+1) < contradiction
pub fn CellValue(comptime T: type) type {
    return union(enum) {
        nothing,
        value: T,
        contradiction: struct { a: T, b: T },
    };
}

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

## Oracle Implementations (in order of authority)

### 1. Registry Oracle (highest authority)

```bash
# Requirement: skills.json entry exists with "trit" field
jq -r --arg name "$SKILL_NAME" \
  '.skills[] | select(.name == $name) | .trit' \
  ~/i/asi/skills.json
# Output: -1 | 0 | 1
# If not found: CellValue.nothing
```

### 2. Structural Oracle

```python
ROLE_TO_TRIT = {
    "VALIDATOR": -1,
    "ERGODIC":    0,
    "BRIDGE":     0,
    "GENERATOR": +1,
}

def structural_oracle(skill_path: str):
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
SKILL_DESC="$1"
TOKEN=$(gcloud auth print-access-token)
PROJECT=$(gcloud config get project 2>/dev/null)

RESPONSE=$(curl -s -X POST \
  "https://us-central1-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/us-central1/publishers/google/models/gemini-2.0-flash:generateContent" \
  -H "Authorization: Bearer ${TOKEN}" \
  -H "Content-Type: application/json" \
  -d "{
    \"contents\": [{\"role\": \"user\", \"parts\": [{\"text\": \"Classify this skill as exactly one of: -1 (validates/constrains), 0 (mediates/routes), or +1 (creates/composes). Respond with ONLY the number. Skill: ${SKILL_DESC}\"}]}],
    \"generationConfig\": {\"temperature\": 0.0, \"maxOutputTokens\": 4}
  }" | jq -r '.candidates[0].content.parts[0].text' | tr -d '[:space:]')

case "$RESPONSE" in
  "-1"|"0"|"1"|"+1") echo "${RESPONSE/+/}" ;;
  *) echo "nothing" ;;
esac
```

### 4. Propagator Network Oracle

```python
def propagator_oracle(skill_name: str):
    """Accumulate trit evidence from all sources via latticeMerge."""
    cell = CellValue.nothing()

    cell = lattice_merge(cell, registry_oracle(skill_name))
    if cell.is_contradiction():
        return cell

    cell = lattice_merge(cell, structural_oracle(skill_path(skill_name)))
    if cell.is_contradiction():
        return cell

    if cell.is_nothing():
        cell = lattice_merge(cell, behavioral_oracle(skill_description(skill_name)))

    return cell
```

## Trit Arithmetic (GF(3))

```python
def gf3_add(a: int, b: int) -> int:
    raw = (a + b) % 3
    return raw if raw <= 1 else raw - 3

def gf3_mul(a: int, b: int) -> int:
    raw = (a * b) % 3
    return raw if raw <= 1 else raw - 3

def is_valid_triad(t1: int, t2: int, t3: int) -> bool:
    return gf3_add(gf3_add(t1, t2), t3) == 0

def build_triad(t1: int, t2: int) -> int:
    """Given two trits, compute the unique third that conserves GF(3)."""
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
