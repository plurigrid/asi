# Monotonic Skill Invariant

## The Law

```
|skills(t+1)| ≥ |skills(t)|   UNLESS   ∃ human_action(t) ∈ DELETE
```

Skills are **discovered**, not invented, through collision with:
- Existing TUI (batrachian toad / ACP surface)
- Droid marketplace (Codex/IES `.agents/skills/`)
- Claude marketplace (`~/.claude/skills/`)

The count **ratchets up monotonically**. The only operation that decreases it
requires **human oversight** — a conscious deletion, not automated cleanup.

## Current Census (2026-02-18)

```
Surface                    Count   Name Limit
─────────────────────────────────────────────
asi/skills/                1,342   none
.agents/skills/ (Codex)    1,183   none
~/.claude/skills/ (Claude)   654   64 chars
asi/plugins/asi/skills/      585   none
─────────────────────────────────────────────
Deduplicated union:        1,360   —
In all three surfaces:       627   —
Unique to asi/ only:         150   —
Unique to .agents/ only:      16   —
Unique to claude/ only:        1   —
```

**Monotonic floor: 1,360**

## Enforcement

### Pre-commit Hook

`asi/.git/hooks/pre-commit` validates that `skills.json:total` never drops
below `skills.json:monotonic_floor` unless `HUMAN_DELETE=1` is set:

```bash
# Normal commit — blocked if count decreases:
git commit -m "skills: update"

# Human-supervised deletion — allowed:
HUMAN_DELETE=1 git commit -m "skills: remove deprecated X (human oversight)"
```

### 64-char Namespace Bridge

One skill exceeds Claude's 64-char directory name limit:

| Long Name (Codex) | Short Name (Claude) | Chars |
|--------------------|---------------------|-------|
| `amp-continue-thread-based-conversation-continuation-with-gf-3-branching` | `amp-gf3-continuation` | 21 |

The `name` field in SKILL.md frontmatter is the canonical identity.
Directory names are derived, not authoritative.

## GF(3) Conservation

The invariant is the 0-trit (ERGODIC) in the meta-triad:

```
skill-deletion (-1) ⊗ monotonic-floor (0) ⊗ skill-discovery (+1) = 0 ✓
```

- **-1**: Deletion requires human energy input (dissipative)
- **0**: The floor is the conserved quantity (ergodic)
- **+1**: Discovery is the natural generative direction (entropic)

## Why This Matters

Without monotonicity, automated agents could:
- Prune "unused" skills they don't understand
- Merge skills, losing interface surface area
- GC skills that serve as future collision targets

The invariant ensures the **possibility space only expands**.
Human oversight is the only legitimate entropy-reversing operation.
