---
name: claude-questions-leaderboard
description: 'Track Claude''s best and worst questions in DuckDB. Use when Claude asks a notably good or bad question, or to review question quality. Triggers: leaderboard, bad question, good question, question quality.'
---

# Claude Questions Leaderboard

DB: `/Users/alice/v/claude_questions_leaderboard.duckdb`
Script: `python3 /Users/alice/.claude/skills/claude-questions-leaderboard/scripts/leaderboard.py`

## Operations

```bash
python3 scripts/leaderboard.py show [bad|good]
python3 scripts/leaderboard.py bad "question" "context" "why bad"
python3 scripts/leaderboard.py good "question" "context" "why insightful"
```

## When to add entries

Context and why fields MUST be grounded in the actual interaction — quote what the user said, describe what Claude did and didn't do, reference the tools that were or weren't used. Do not write generic descriptions.

**Bad**: Claude asked a question when tools could have answered it. Claude assumed the user was wrong. Claude didn't use available skills/MCPs before asking.

**Good**: Claude asked something that reframed the problem, surfaced a hidden connection, or showed real understanding of intent. NOT "delivering well" — the question itself must be insightful.

## Principle
Exhaust tools before asking. When you do ask, ask something worth asking.


## Para(Optic) atlas

Part of: `para-mensch-commons`.
