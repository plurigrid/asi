---
name: local-finetune
description: local-finetune
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# local-finetune

> Local model fine-tuning pipeline using ACSets + DuckDB + MLX

**Trit**: 0 (Coordinator - orchestrates data flow)
**Bundle**: substrate
**Requires**: duckdb, mlx-lm, acsets skill

## Overview

Pipeline for embedding skills into local models via LoRA fine-tuning on Apple Silicon.

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   ACSets    │───▶│   DuckDB    │───▶│   JSONL     │───▶│  mlx-lm     │
│   Schema    │    │   Corpus    │    │  Training   │    │  LoRA       │
└─────────────┘    └─────────────┘    └─────────────┘    └─────────────┘
```

## Database Location

```
~/skill-substrate/skill_corpus.duckdb
```

## Schema (ACSet-inspired)

```sql
-- Objects: Skill, Example, Category
-- Morphisms: skill_of, category_of, trit_of

CREATE TABLE skills (
    id INTEGER PRIMARY KEY,
    name VARCHAR UNIQUE,
    description TEXT,
    location VARCHAR,
    fingerprint UBIGINT,
    color_hex VARCHAR,
    trit INTEGER CHECK (trit IN (-1, 0, 1))
);

CREATE TABLE examples (
    id INTEGER PRIMARY KEY,
    skill_id INTEGER REFERENCES skills(id),
    instruction TEXT NOT NULL,
    input TEXT,
    output TEXT,
    fingerprint UBIGINT,
    trit INTEGER
);

CREATE TABLE claude_history (
    id INTEGER,
    content TEXT,
    ts TIMESTAMP,
    project VARCHAR,
    sessionId VARCHAR,
    fingerprint UBIGINT,
    color_hex VARCHAR,
    trit INTEGER
);
```

## Ingest Claude History

```sql
CREATE TABLE claude_history AS
SELECT
    row_number() OVER () as id,
    display as content,
    to_timestamp(timestamp/1000) as ts,
    project,
    sessionId,
    hash(display || COALESCE(project,'')) as fingerprint,
    '#' || printf('%06x', ABS(hash(display)) % 16777216) as color_hex,
    CAST(ABS(hash(display)) % 3 AS INTEGER) - 1 as trit
FROM read_json('~/.claude/history.jsonl',
    format='newline_delimited',
    ignore_errors=true,
    columns={display: 'VARCHAR', timestamp: 'BIGINT', project: 'VARCHAR', sessionId: 'VARCHAR'}
)
WHERE display IS