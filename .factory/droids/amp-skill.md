---
name: amp-skill
description: Interruption pattern detection and retrieval from Amp thread history. Use for analyzing tool rejection patterns and improving agent behavior.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Amp-Skill: Interruption Pattern Detection and Retrieval

**GF(3) Trit**: 0 (ERGODIC - coordination layer)
**Foundation**: DuckDB ACSet from Amp file-changes

## Overview

Amp-Skill distills usage patterns from Amp thread history, specifically focusing on **interruption patterns** where tool suggestions were rejected in favor of:
1. **Two-lock processes** - user requested confirmation before proceeding
2. **Complete discontinuation** - user abandoned the thread entirely
3. **Reverted operations** - user explicitly undid an AI action

## Retrieval Benchmark Metrics

| Metric | Value |
|--------|-------|
| Total Threads | 616 |
| Total Tool Calls | 2,535 |
| Threads with Interruptions | 282 (45.8%) |
| Reverted Tool Calls | 84 (3.3%) |
| Two-Lock Cascades | 47 |
| Complete Discontinuations | 22 |

## Interruption Pattern Distribution

| Pattern Type | Count | Percentage |
|--------------|-------|------------|
| abandoned | 269 | 62.4% |
| reverted | 84 | 19.5% |
| two_lock | 47 | 10.9% |
| discontinuation | 22 | 5.1% |
| high_rejection | 9 | 2.1% |

## GF(3) Distribution

| Role | Threads | Tool Calls | Reverted |
|------|---------|------------|----------|
| MINUS | 218 | 769 | 27 |
| ERGODIC | 209 | 976 | 26 |
| PLUS | 189 | 790 | 31 |

## File Types Most Frequently Reverted

1. `.org` - 28 reverts (Emacs org-mode files)
2. `.py` - 20 reverts (Python scripts)
3. `.sh` - 18 reverts (Shell scripts)
4. `.md` - 15 reverts (Markdown documentation)

## SQL Access

```sql
-- Query interruption patterns
SELECT * FROM amp_interruptions ORDER BY ts DESC;

-- Find high-rejection threads
SELECT thread_id, tool_call_count, reverted_count,
       ROUND(100.0 * reverted_count / tool_call_count, 1) as revert_pct
FROM amp_threads
WHERE reverted_count > 0
ORDER BY revert_pct DESC;

-- Detect two-lock cascades
SELECT thread_id, COUNT(*) as consecutive_reverts
FROM amp_interruptions
WHERE pattern_type = 'two_lock'
GROUP BY thread_id
ORDER BY consecutive_reverts DESC;
```

## Key Insigh