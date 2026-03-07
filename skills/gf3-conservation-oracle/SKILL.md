---
name: gf3-conservation-oracle
description: >
  Formal oracle verifying GF(3) trit conservation across skill triads.
  Triggers: verify trit conservation, check GF(3) invariant, pre-commit trit check,
  triad validation, conservation law enforcement, sum mod 3 check.
---

# GF(3) Conservation Oracle

## Formal Specification

### Type

```
ConservationOracle : SkillGraph -> ConservationResult

ConservationResult =
  | CONSERVED   { certificate: list[ValidTriad] }
  | VIOLATED    { witness: ViolatingTriad }
  | UNKNOWN     { reason: string }

ValidTriad     = (s1, s2, s3, trits) where trit(s1) + trit(s2) + trit(s3) = 0 mod 3
ViolatingTriad = (s1, s2, s3, trits) where trit(s1) + trit(s2) + trit(s3) != 0 mod 3
```

### Preconditions

1. SkillGraph has at least 3 skills
2. Every skill has a trit in {-1, 0, +1}
3. "Valid triad" means: three skills are connected (edge or hub connection)

### Postconditions

1. Returns EXACTLY ONE of: `CONSERVED` | `VIOLATED` | `UNKNOWN`
2. `CONSERVED` is witnessed by an explicit list of checked triads
3. `VIOLATED` provides the FIRST violating triad found
4. `UNKNOWN` only if a skill has undefined trit
5. Deterministic: same graph state -> same result

## GF(3) Arithmetic

```python
def gf3_rep(x: int) -> int:
    """Map any integer to canonical GF(3) representative in {-1, 0, +1}."""
    r = x % 3
    return r if r <= 1 else r - 3

def gf3_add(a: int, b: int) -> int:
    return gf3_rep(a + b)

def gf3_sum(*args: int) -> int:
    result = 0
    for a in args:
        result = gf3_add(result, a)
    return result

def is_valid_triad(t1: int, t2: int, t3: int) -> bool:
    """Conservation law: t1 + t2 + t3 = 0 (mod 3)."""
    return gf3_sum(t1, t2, t3) == 0

def third_trit(t1: int, t2: int) -> int:
    """Given two trits, compute the unique third conserving GF(3)."""
    return gf3_rep(-(t1 + t2))
```

## Oracle Implementation

```python
from dataclasses import dataclass
import json

@dataclass
class SkillNode:
    name: str
    trit: int
    role: str

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
    edges: list[tuple[str, str]],
    check_all: bool = False,
) -> dict:
    """
    Requirement:  all skills have trit in {-1, 0, +1}
    Postcondition: returns CONSERVED | VIOLATED | UNKNOWN
    """
    skill_map = {s.name: s for s in skills}
    for skill in skills:
        if skill.trit not in (-1, 0, 1):
            return {"result": "UNKNOWN", "reason": f"Skill '{skill.name}' has undefined trit"}

    adj = {s.name: set() for s in skills}
    for (a, b) in edges:
        adj[a].add(b)
        adj[b].add(a)

    violations = []
    valid_triads = []

    skill_names = list(skill_map.keys())
    for i, n1 in enumerate(skill_names):
        for n2 in skill_names[i+1:]:
            if n2 not in adj[n1]:
                continue
            for n3 in skill_names:
                if n3 == n1 or n3 == n2:
                    continue
                if n3 not in adj[n1] and n3 not in adj[n2]:
                    continue

                s1, s2, s3 = skill_map[n1], skill_map[n2], skill_map[n3]
                triad = Triad(s1, s2, s3)

                if triad.is_valid:
                    valid_triads.append({
                        "skills": [n1, n2, n3],
                        "trits": [s1.trit, s2.trit, s3.trit],
                    })
                else:
                    violations.append({
                        "skills": [n1, n2, n3],
                        "trits": [s1.trit, s2.trit, s3.trit],
                        "sum_mod3": triad.trit_sum
                    })
                    if not check_all:
                        return {"result": "VIOLATED", "witness": violations[0]}

    if violations:
        return {"result": "VIOLATED", "witness": violations[0],
                "all_violations": violations if check_all else None}

    return {"result": "CONSERVED", "certificate": valid_triads,
            "triads_checked": len(valid_triads)}
```

## Pre-Commit Hook

```bash
#!/usr/bin/env bash
# .git/hooks/pre-commit
set -euo pipefail

SKILLS_JSON="$HOME/i/asi/skills.json"
ORACLE_SCRIPT="$HOME/i/asi/skills/gf3-conservation-oracle/check.py"

CHANGED_SKILLS=$(git diff --cached --name-only | grep 'skills/' | cut -d/ -f1-3 | sort -u)

if [ -z "$CHANGED_SKILLS" ]; then
    exit 0
fi

echo "GF(3) Conservation Oracle: checking changed skills..."

python3 "$ORACLE_SCRIPT" \
    --skills-json "$SKILLS_JSON" \
    --changed-skills "$CHANGED_SKILLS" \
    --mode "pre-commit"

STATUS=$?
if [ $STATUS -ne 0 ]; then
    echo "BLOCKED: GF(3) conservation violated."
    echo "Use: third_trit(t1, t2) to compute the required third trit."
    exit 1
fi

echo "GF(3) conservation: CONSERVED. Commit allowed."
```

## Monotonic Skill Invariant

```python
def monotonic_oracle(old_skills_json: str, new_skills_json: str) -> dict:
    """
    Separate from GF(3) conservation -- both must hold.
    Postcondition: CONSERVED if new_count >= old_count, VIOLATED otherwise.
    """
    old_count = len(json.load(open(old_skills_json))["skills"])
    new_count = len(json.load(open(new_skills_json))["skills"])

    if new_count >= old_count:
        return {"result": "CONSERVED", "old_count": old_count,
                "new_count": new_count, "delta": new_count - old_count}
    else:
        return {"result": "VIOLATED", "witness": {
            "old_count": old_count, "new_count": new_count}}
```

## Dafny Formal Verification

```dafny
lemma GF3Conservation(t1: int, t2: int, t3: int)
    requires t1 in {-1, 0, 1} && t2 in {-1, 0, 1} && t3 in {-1, 0, 1}
    requires (t1 + t2 + t3) % 3 == 0
    ensures third_trit(t1, t2) == t3
{
    // Proof by exhaustive case analysis (27 cases) -- Dafny verifies via SAT
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

## What This Oracle Is NOT

- NOT a style checker -- conservation is a mathematical invariant
- NOT a majority vote -- one violation invalidates the entire graph
- NOT approximate -- exact mod 3, no tolerance
- NOT transitive -- CONSERVED for subgraph does NOT imply CONSERVED for full graph
