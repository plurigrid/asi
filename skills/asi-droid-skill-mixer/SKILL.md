---
name: asi-droid-skill-mixer
description: "Ensures droid configs (26 world-*.md) and skill catalog (1210 skills) are cross-referenced and mixed. Detects orphaned droids without skills and skills without droids. The missing integration layer."
trit: -1
version: 1.0.0
seed: 1069
triad: "asi-droid-skill-mixer (-1) ⊗ asi-sheaf-coordinator (0) ⊗ asi-letter-bootstrap (+1) = 0"
---

# ASI Droid-Skill Mixer

> "check droid skills to make sure we have not forgotten to mix in"

## Role: MINUS (-1) — Validate Cross-References

### The Problem

Two independent registries exist:
1. **Droid configs**: `~/.factory/droids/world-{a..z}.md` (26 files)
2. **Skill catalog**: `~/worlds/z/.agents/skills/` (1210 directories)

Nothing ensures they're mixed. A droid can exist without any matching skill.
A skill can reference a letter that has no droid.

### Cross-Reference Matrix

For each letter a-z:

| Check | Source | Target |
|---|---|---|
| Droid exists | `~/.factory/droids/world-<letter>.md` | must exist |
| Droid has trit | frontmatter `trit` field | must be -1, 0, or +1 |
| Droid has stratum | description field | must be physics/substrate/type/games/money |
| Droid has security role | description field | must be non-empty |
| Skills reference letter | grep skills for letter mentions | at least 1 skill |
| .sb profile matches trit | `/tmp/sb/world-<letter>.sb` trit comment | must match droid |
| Skill triad is conserved | skill SKILL.md triad field | sum ≡ 0 (mod 3) |

### What We Found Missing

From reading plurigrid/asi skills:

1. **plurigrid-asi-integrated**: Letter index has 8 of 26 letters. Missing 18.
2. **asi-integrated**: Contradictory trit (-1 AND 0). Needs resolution.
3. **asi-skill-selector**: Reports 186/443 skills with trits (42%). No per-letter view.
4. **asi-polynomial-operads**: Pure theory, no runtime enforcement.
5. **worlds/v/asi/**: 3 skills (session-capture, warehouse-network, whitehole-audio).
   warehouse-network has NO trit. No triad formed.

### Mixer Output

```
DROID-SKILL MIX REPORT
═══════════════════════

Droids: 26/26 (complete)
Skills with trits: 186/1210 (15%)
Skills per letter: [varies]

ORPHANED DROIDS (no matching skill):
  [none — all 26 have at least the seatbelt enforcement skills]

ORPHANED SKILLS (no matching letter):
  warehouse-network (worlds/v) — no trit
  [257 skills without trit assignments]

TRIAD VIOLATIONS:
  asi-integrated — contradictory trit (-1 and 0)
  worlds/v/asi — no triad among 3 skills

PROPOSED FIXES:
  1. Assign trit to warehouse-network: -1 (infrastructure validation)
  2. Resolve asi-integrated trit: assign -1 (verification role matches description)
  3. Form worlds/v triad: session-capture(0) ⊗ warehouse-network(-1) ⊗ whitehole-audio(0)
     Sum = -1 ≡ 2 (mod 3) — VIOLATION. Need to adjust one trit.
     Fix: whitehole-audio → +1, then 0 + (-1) + 1 = 0 ✓
```

### Integration

- Runs as pre-commit hook alongside gf3-conservation-oracle
- Feeds into asi-sheaf-coordinator for gluing verification
- Triggers asi-letter-bootstrap when gaps are found
