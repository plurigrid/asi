---
name: skill-finder-verifier
description: 'Find locally-created skills and verify provenance. Distinguishes locally-created from batch-installed by diffing against asi/skills/ baseline. Evaluates modified downloads for functional improvement. Triggers: new skills, local skills, skill audit, skill provenance, skill verification.'
---

# Skill Finder & Verifier

Script: `python3 /Users/alice/.claude/skills/skill-finder-verifier/scripts/finder.py`
Baseline: `/Users/alice/v/asi/skills/` (upstream plurigrid/asi)

## Operations

```bash
# Scan all directories, classify every skill
python3 scripts/finder.py scan

# Scan a single location (agents|claude|codex|goose|copilot|openhands)
python3 scripts/finder.py scan claude

# Verify a specific skill's provenance
python3 scripts/finder.py verify ducklake

# Show diff between local and asi version
python3 scripts/finder.py diff basin
```

## Classification

- **local-only**: Not in asi/skills/ at all. Genuinely created here.
- **modified**: Exists in asi but SKILL.md differs. Candidate for "functionally better" evaluation.
- **identical**: Same hash as asi. Batch-installed, unmodified.
- **identical-md-extra-files**: SKILL.md matches but local has additional files (scripts, assets).

## Evaluating Modified Skills

When a skill is classified as **modified**, evaluate whether the changes make it functionally better by loading these 5 skills:

1. **sharp-edges** — Does the modified version fix footgun designs or dangerous defaults?
2. **refuse-mediocrity** — Does it raise the quality bar vs the generic upstream?
3. **code-review** — Are any added scripts well-written and correct?
4. **hogwash-removal** — Does it strip filler and add substance?
5. **skill-validation-gf3** — Does it maintain valid skill structure?

A modified skill counts as "functionally better" when it meets **3+ of 5** evaluator criteria:
- Adds environment-specific instructions the upstream lacks
- Includes working scripts/assets the upstream doesn't have
- Fixes incorrect or misleading guidance
- Removes generic filler, adds grounded instructions
- Maintains valid SKILL.md structure with proper frontmatter

## What This Skill Is NOT

Not a batch installer. Not for downloading skills. Only for finding what's already here and verifying its provenance.
