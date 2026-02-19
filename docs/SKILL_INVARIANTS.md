# Skill Invariants

This repository enforces two structural invariants:

1. `skill_dirs` must be non-decreasing.
2. `reachability_cost` must not increase, and must strictly decrease when `skill_dirs` grows.
3. Locally dense time: metric-changing transitions must stay below a configured time-gap bound.

Both invariants can be waived only with explicit human oversight.

## Why

The intent is to preserve discoverability as the skill catalog expands:
- The skill count should not shrink silently.
- Reachability from the 17 hub skills should improve over time, not regress.

## Checker

Use:

```bash
python3 scripts/enforce_skill_invariants.py
```

By default, when run inside a Git repository, the checker uses **tracked**
skill directories only. This avoids false failures from local untracked skill
experiments.

Bootstrap/update baseline:

```bash
python3 scripts/enforce_skill_invariants.py --update-state
```

Include untracked local skills explicitly:

```bash
python3 scripts/enforce_skill_invariants.py --include-untracked
```

Emit an Anoma/Juvix transition intent payload:

```bash
python3 scripts/enforce_skill_invariants.py \
  --emit-intent /tmp/reachability-intent.json
```

The emitted payload has type `ReachabilityInvariantIntent` and includes:
- previous/next `(skill_count, reachability_cost, generated_at, tick)`
- evaluated constraint booleans
- locally dense time metadata (`metrics_changed`, `delta_seconds`)
- oversight metadata
- a deterministic `witness` hash

## Human Oversight Override

When an intentional exception is required, pass an explicit note:

```bash
python3 scripts/enforce_skill_invariants.py \
  --human-oversight \
  --oversight-note "Intentional consolidation after manual review"
```

Equivalent environment form:

```bash
ASI_HUMAN_OVERSIGHT=1 \
ASI_HUMAN_OVERSIGHT_NOTE="Intentional consolidation after manual review" \
python3 scripts/enforce_skill_invariants.py
```

## Files

- `invariants/skill_invariants_config.json`: hub set + seed/pattern edges + policy.
- `invariants/skill_invariants_state.json`: baseline metrics used for regression checks.
- `formalization/SkillReachabilityInvariant.juvix`: Anoma/Juvix policy expression.

Temporal density is configured via:
- `policy.max_seconds_between_snapshots` (currently `2592000`, i.e. 30 days)

Note: the time-gap check is applied when the computed metrics change relative to baseline
(i.e. an actual transition), not on identical re-checks.

## CI

The invariant checker is wired into:
- `scripts/validate_plugin.sh`
- `.github/workflows/validate.yml`
