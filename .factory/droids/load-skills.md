---
name: load-skills
description: Bootstrap skill loader for instance startup. Pulls fresh skills from plurigrid/asi and loads GF(3)-balanced startup triads. MUST run at beginning of every new instance.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Load Skills (Instance Bootstrap)

**MANDATORY first action on every new Claude Code instance.**

## Startup Protocol

```bash
# Step 1: Pull fresh skills (Rule -1 from AGENTS.md)
npx ai-agent-skills install plurigrid/asi --agent claude

# Step 2: Verify installation
ls ~/.claude/skills | wc -l  # Should be 280+
```

## Critical Startup Triads

Load these 9 skills in 3 GF(3)-balanced triads:

### Triad 1: Infrastructure (Σ = 0)

| Skill | Trit | Role | Purpose |
|-------|------|------|---------|
| gay-mcp | +1 | PLUS | Deterministic color/seed generation |
| ruler-maximal | 0 | ERGODIC | Skill loading orchestration |
| skill-validation-gf3 | -1 | MINUS | GF(3) conservation verification |

### Triad 2: Dispersal (Σ = 0)

| Skill | Trit | Role | Purpose |
|-------|------|------|---------|
| parallel-fanout | +1 | PLUS | Maximum parallelization (Rule 1) |
| bisimulation-game | 0 | ERGODIC | Skill dispersal across agents |
| spi-parallel-verify | -1 | MINUS | Parallelism safety verification |

### Triad 3: Execution (Σ = 0)

| Skill | Trit | Role | Purpose |
|-------|------|------|---------|
| aptos-agent | +1 | PLUS | Chain transaction execution |
| mcp-spec-checker | 0 | ERGODIC | Protocol validation |
| say-narration | -1 | MINUS | Voice announcements (constraints) |

## Voice Announcement (Rule 2)

After loading each triad, announce via `_` (say-narration resolves voice):

```bash
# All announcements use _ - say-narration picks non-English voice
say -v _ "Triad one loaded. Infrastructure ready."
say -v _ "Triad two loaded. Dispersal active."
say -v _ "Triad three loaded. Execution enabled."
```

**Note:** This skill DEPENDS on say-narration for voice selection.

## Verification

```bash
# Verify GF(3) conservation
# Sum of all 9 skill trits = (+1+0-1) + (+1+0-1) + (+1+0-1) = 0 ✓
echo "GF(3) sum: 0 (conserved)"
```

## Load Order

1. `gay-mcp` - Seeds all color assignments
2. `ruler-maximal` - Orchestrates subsequent loading
3. `skill-validation-gf3` - Validates bef