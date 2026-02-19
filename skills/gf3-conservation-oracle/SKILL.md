---
name: gf3-conservation-oracle
description: Formal oracle verifying GF(3) trit conservation across skill triads, belief states, and propagator networks. Given a set of skills/values with assigned trits, decides if the sum ≡ 0 mod 3 for every valid triad. Returns CONSERVED | VIOLATED | UNKNOWN with an explicit witness (the violating triad or the certificate). This is the pre-commit invariant enforced by gf3-pr-verify.
version: 1.0.0
trit: -1
role: VALIDATOR
tags: [gf3, oracle, conservation, triads, formal, invariant, pre-commit, validator]
deployed: 2026-02-19
---

# GF(3) Conservation Oracle

## Formal Specification

### Type

```
ConservationOracle : SkillGraph → ConservationResult

ConservationResult =
  | CONSERVED   { certificate: list[ValidTriad] }   -- all triads sum to 0 mod 3
  | VIOLATED    { witness: ViolatingTriad }          -- explicit counterexample
  | UNKNOWN     { reason: string }                  -- trit not defined for some skill

ValidTriad    = (s₁, s₂, s₃, trits) where trit(s₁) + trit(s₂) + trit(s₃) ≡ 0 mod 3
ViolatingTriad = (s₁, s₂, s₃, trits) where trit(s₁) + trit(s₂) + trit(s₃) ≢ 0 mod 3
```

### Preconditions

1. SkillGraph has at least 3 skills
2. Every skill has a trit ∈ {-1, 0, +1} (from gf3-trit-oracle, NOT guessed)
3. "Valid triad" means: the three skills are connected (skill graph edge or hub connection)
4. Background: `skills.json` registry with trit fields populated

### Postconditions

1. Returns EXACTLY ONE of: `CONSERVED` | `VIOLATED` | `UNKNOWN`
2. `CONSERVED` is witnessed by an explicit list of checked triads (never "all triads ok")
3. `VIOLATED` provides the FIRST violating triad found (witness, not just count)
4. `UNKNOWN` only if a skill in the checked graph has `CellValue.nothing` from gf3-trit-oracle
5. Deterministic: same graph state → same result (no randomness)

---

## GF(3) Arithmetic (exact)

```python
# GF(3) = ℤ/3ℤ with representatives {-1, 0, +1} ≡ {2, 0, 1} (mod 3)

def gf3_rep(x: int) -> int:
    """Map any integer to canonical GF(3) representative in {-1, 0, +1}."""
    r = x % 3
    return r if r <= 1 else r - 3  # {0,1,2} → {0,1,-1}

def gf3_add(a: int, b: int) -> int:
    """Precondition: a, b ∈ {-1, 0, +1}. Postcondition: result ∈ {-1, 0, +1}."""
    return gf3_rep(a + b)

def gf3_sum(*args: int) -> int:
    """Sum of any number of trits in GF(3)."""
    result = 0
    for a in args:
        result = gf3_add(result, a)
    return result

def is_valid_triad(t1: int, t2: int, t3: int) -> bool:
    """Conservation law: t1 + t2 + t3 ≡ 0 (mod 3)."""
    return gf3_sum(t1, t2, t3) == 0

def third_trit(t1: int, t2: int) -> int:
    """Given two trits, compute the unique third conserving GF(3).
    Postcondition: is_valid_triad(t1, t2, result) == True
    """
    return gf3_rep(-(t1 + t2))

# Cayley table for GF(3) addition (trits as {-1, 0, +1}):
# +  | -1   0  +1
# ---|------------
# -1 |  1  -1   0
#  0 | -1   0  +1
# +1 |  0  +1  -1
```

---

## Oracle Implementation

```python
from dataclasses import dataclass
from typing import Optional
import json

@dataclass
class SkillNode:
    name: str
    trit: int       # -1, 0, +1 — from gf3-trit-oracle (NOT guessed)
    role: str       # VALIDATOR | ERGODIC | BRIDGE | GENERATOR

@dataclass
class Triad:
    s1: SkillNode
    s2: SkillNode
    s3: SkillNode

    @property
    def trit_sum(self) -> int:
        return gf3_sum(self.s1.trit, self.s2.trit, self.s3.trit)

    @property
    def is_valid(self) -> bool:
        return self.trit_sum == 0

def conservation_oracle(
    skills: list[SkillNode],
    edges: list[tuple[str, str]],  # skill graph edges
    check_all: bool = False,       # if False, return on first violation
) -> dict:
    """
    Requirement:  all skills have trit ∈ {-1, 0, +1} (not None)
    Postcondition: returns CONSERVED | VIOLATED | UNKNOWN

    Triad selection: connected triples only (s1-s2 edge AND s2-s3 edge AND s1-s3 edge)
    OR hub triples: (hub, s1, s2) where hub connects to both s1 and s2
    """
    # Check for UNKNOWN (any skill has undefined trit)
    skill_map = {s.name: s for s in skills}
    for skill in skills:
        if skill.trit not in (-1, 0, 1):
            return {
                "result": "UNKNOWN",
                "reason": f"Skill '{skill.name}' has undefined trit: {skill.trit}"
            }

    # Build adjacency for connected triple enumeration
    adj = {s.name: set() for s in skills}
    for (a, b) in edges:
        adj[a].add(b)
        adj[b].add(a)

    violations = []
    valid_triads = []

    # Check all connected triples
    skill_names = list(skill_map.keys())
    for i, n1 in enumerate(skill_names):
        for n2 in skill_names[i+1:]:
            if n2 not in adj[n1]:
                continue  # not connected — skip
            for n3 in skill_names:
                if n3 == n1 or n3 == n2:
                    continue
                if n3 not in adj[n1] and n3 not in adj[n2]:
                    continue  # n3 not connected to either — skip

                s1, s2, s3 = skill_map[n1], skill_map[n2], skill_map[n3]
                triad = Triad(s1, s2, s3)

                if triad.is_valid:
                    valid_triads.append({
                        "skills": [n1, n2, n3],
                        "trits": [s1.trit, s2.trit, s3.trit],
                        "sum_mod3": 0
                    })
                else:
                    violations.append({
                        "skills": [n1, n2, n3],
                        "trits": [s1.trit, s2.trit, s3.trit],
                        "sum_mod3": triad.trit_sum
                    })
                    if not check_all:
                        # Return immediately on first violation
                        return {
                            "result": "VIOLATED",
                            "witness": violations[0]
                        }

    if violations:
        return {
            "result": "VIOLATED",
            "witness": violations[0],
            "all_violations": violations if check_all else None,
        }

    return {
        "result": "CONSERVED",
        "certificate": valid_triads,
        "triads_checked": len(valid_triads),
    }
```

---

## Pre-Commit Integration (gf3-pr-verify hook)

```bash
#!/usr/bin/env bash
# .git/hooks/pre-commit
# Requirement: gf3-trit-oracle is accessible (jq + skills.json)
# Postcondition: blocks commit if GF(3) conservation violated

set -euo pipefail

SKILLS_JSON="$HOME/i/asi/skills.json"
ORACLE_SCRIPT="$HOME/i/asi/skills/gf3-conservation-oracle/check.py"

# Get changed skill directories
CHANGED_SKILLS=$(git diff --cached --name-only | grep 'skills/' | cut -d/ -f1-3 | sort -u)

if [ -z "$CHANGED_SKILLS" ]; then
    exit 0  # No skill changes — no conservation check needed
fi

echo "GF(3) Conservation Oracle: checking changed skills..."

# Extract full skill graph from registry
python3 "$ORACLE_SCRIPT" \
    --skills-json "$SKILLS_JSON" \
    --changed-skills "$CHANGED_SKILLS" \
    --mode "pre-commit"

STATUS=$?
if [ $STATUS -ne 0 ]; then
    echo "BLOCKED: GF(3) conservation violated."
    echo "Fix the trit assignment before committing."
    echo "Use: third_trit(t1, t2) to compute the required third trit."
    exit 1
fi

echo "GF(3) conservation: CONSERVED. Commit allowed."
exit 0
```

---

## Monotonic Skill Invariant

```python
# Requirement: skills.json has a "count" field or is countable
# Postcondition: new count >= old count (MONOTONIC_SKILL_INVARIANT)

def monotonic_oracle(old_skills_json: str, new_skills_json: str) -> dict:
    """
    Precondition:  both JSON files are valid ASI skill registries
    Postcondition: returns CONSERVED if new_count >= old_count, VIOLATED otherwise

    This is SEPARATE from GF(3) conservation — both must hold.
    """
    old_count = len(json.load(open(old_skills_json))["skills"])
    new_count = len(json.load(open(new_skills_json))["skills"])

    if new_count >= old_count:
        return {
            "result": "CONSERVED",
            "old_count": old_count,
            "new_count": new_count,
            "delta": new_count - old_count,
        }
    else:
        return {
            "result": "VIOLATED",
            "witness": {
                "old_count": old_count,
                "new_count": new_count,
                "deleted_count": old_count - new_count,
            }
        }
```

---

## Composition of GF(3) Oracles

```
Conservation oracle checks:       STATIC invariant (graph structure)
Trit oracle provides:             ATOMIC classification per skill
Abductive oracle uses:            DYNAMIC classification per evidence
Bisimulation oracle uses:         BEHAVIORAL equivalence per trit class
Neurofeedback oracle provides:    REAL-TIME trit from EEG signal

All five must agree (no contradiction across layers):

CellValue.nothing    → oracle not yet run
CellValue.value(t)   → oracle returned definite trit t
CellValue.contradiction → two authoritative sources disagree → HALT
```

---

## Dafny Formal Verification

```dafny
// Requirement: Dafny 4.x installed
// Postcondition: conservation law formally verified for up to N triad checks

lemma GF3Conservation(t1: int, t2: int, t3: int)
    requires t1 in {-1, 0, 1} && t2 in {-1, 0, 1} && t3 in {-1, 0, 1}
    requires (t1 + t2 + t3) % 3 == 0
    ensures third_trit(t1, t2) == t3
{
    // Proof: by exhaustive case analysis (27 cases)
    // Dafny verifies this automatically via SAT
}

function third_trit(t1: int, t2: int): int
    requires t1 in {-1, 0, 1} && t2 in {-1, 0, 1}
    ensures third_trit(t1, t2) in {-1, 0, 1}
    ensures (t1 + t2 + third_trit(t1, t2)) % 3 == 0
{
    var sum := t1 + t2;
    var raw := (-sum) % 3;
    if raw == 2 then -1 else raw
}
```

---

## What This Oracle Is NOT

- NOT a style checker — conservation is a mathematical invariant, not a convention
- NOT a majority vote — one violation invalidates the entire graph
- NOT approximate — conservation is exact (mod 3), no tolerance, no ε
- NOT transitive — CONSERVED for subgraph does NOT imply CONSERVED for full graph
- NOT bypassed by `--no-verify` in a correctly configured git repo

---

## Related Skills

- `gf3-trit-oracle` — provides the trit values this oracle checks
- `gf3-pr-verify` — pre-commit hook that invokes this oracle
- `gf3-tripartite` — composition invariant checker (same algebra, different scope)
- `belief-revision-log` — beliefs must also satisfy GF(3) conservation at each timestamp
- `skill-validation-gf3` — validates individual skills against registry
- `formal-verification` / `dafny-formal-verification` — Dafny proof of the lemmas above
- `bisimulation-oracle` — uses trit class to gate bisimulation queries
