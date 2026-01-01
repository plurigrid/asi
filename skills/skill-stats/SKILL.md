---
name: skill-stats
description: Skill statistics, thread usage analysis, GF(3) conservation tracking, and probe verification for the 443+ skill ecosystem
trit: 0
probe: bb -e '(println (count (filter #(.isDirectory %) (file-seq (io/file (str (System/getenv "HOME") "/.claude/skills"))))))'
verify: |
  ls ~/.claude/skills/*/SKILL.md | wc -l
bundle: meta
priority: 1
---

# Skill Stats

Analyze skill ecosystem health, thread usage, and GF(3) conservation.

## Quick Commands

```bash
# Count skills
ls ~/.claude/skills/*/SKILL.md | wc -l

# Trit distribution
grep -h "^trit:" ~/.claude/skills/*/SKILL.md | sort | uniq -c

# Skills with probes
grep -l "^probe:" ~/.claude/skills/*/SKILL.md | wc -l

# Recently modified
ls -lt ~/.claude/skills/*/SKILL.md | head -20
```

## GF(3) Conservation Check

```bash
# Calculate global trit sum
grep -h "^trit:" ~/.claude/skills/*/SKILL.md | \
  awk '{sum += $2} END {print "GF(3) Sum:", sum}'
```

Target: Sum should be 0 (or divisible by 3).

## Thread-Skill Usage Analysis

Use `find_thread` to discover skill usage patterns:

```
find_thread query="skill after:7d" limit=20
```

Then extract skill mentions from thread summaries.

## Probe Verification

Run all skill probes:

```bash
for skill in ~/.claude/skills/*/SKILL.md; do
  name=$(dirname $skill | xargs basename)
  probe=$(grep "^probe:" $skill | sed 's/^probe: *//')
  if [ -n "$probe" ]; then
    echo "Probing: $name"
    eval "$probe" 2>&1 | head -3
  fi
done
```

## Dashboard Generation

```bash
bb ~/ies/scripts/asi_skill_selector.bb list > skill_inventory.txt
```

## Integration with DuckDB

```sql
-- Load skill metadata into DuckDB
CREATE TABLE skill_stats AS
SELECT 
  skill_name,
  trit,
  has_probe,
  last_modified,
  usage_count
FROM read_json('skill_metadata.json');

-- GF(3) balance check
SELECT SUM(trit) as global_balance FROM skill_stats;

-- Most used skills
SELECT skill_name, usage_count 
FROM skill_stats 
ORDER BY usage_count DESC 
LIMIT 20;
```

## Key Metrics

| Metric | Query |
|--------|-------|
| Total skills | `ls ~/.claude/skills/*/SKILL.md \| wc -l` |
| With trit | `grep -l "^trit:" ~/.claude/skills/*/SKILL.md \| wc -l` |
| With probe | `grep -l "^probe:" ~/.claude/skills/*/SKILL.md \| wc -l` |
| MINUS count | `grep -h "^trit: -1" ~/.claude/skills/*/SKILL.md \| wc -l` |
| ERGODIC count | `grep -h "^trit: 0" ~/.claude/skills/*/SKILL.md \| wc -l` |
| PLUS count | `grep -h "^trit: 1" ~/.claude/skills/*/SKILL.md \| wc -l` |

## Skill Health Score

```
Health = (skills_with_trit / total) × (skills_with_probe / total) × (1 - |gf3_sum| / total)
```

Target: Health > 0.8

## Related Skills

- `triadic-skill-orchestrator` (0) - Dispatch balanced triplets
- `asi-skill-selector` (0) - CLI for skill selection
- `bisimulation-game` (-1) - Skill dispersal verification
- `autopoiesis` (0) - Self-modification tracking
