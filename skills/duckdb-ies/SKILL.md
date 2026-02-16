---
name: duckdb-ies
description: ' Layer 4: IES Interactome Analytics with GF(3) Momentum Tracking'
version: 1.0.0
---


# duckdb-ies

> Layer 4: IES Interactome Analytics with GF(3) Momentum Tracking

**Version**: 2.0.0  
**Trit**: +1 (Generative - produces analysis artifacts)  
**Bundle**: analytics  
**Extends**: duckdb-timetravel

## Overview

DuckDB-IES provides unified interactome analytics across Claude history, GitHub activity, workspace files, and skill manifests. It implements GF(3) momentum tracking, topic clustering, and cross-source fingerprint correlation.

## Database Location

```
/Users/bob/ies/ducklake_data/ies_interactome.duckdb
```

## Core Tables

| Table | Rows | Description |
|-------|------|-------------|
| `claude_history_colored` | 1316+ | Claude interactions with Gay.jl coloring |
| `gh_repos_colored` | 50 | GitHub repos with trit values |
| `gh_contributions` | 366 | Daily contribution counts |
| `skill_manifests` | 1+ | Skill metadata with fingerprints |
| `workspace_files` | 200+ | Workspace file index by type |
| `topic_clusters` | 14 | Content-based topic extraction |
| `skill_dependency_graph` | 5 | Skill domain → file mappings |

## Core Views

### unified_interactions
Merges all sources into single stream:
```sql
SELECT timestamp, source, content, category, fingerprint, color_hex, trit
FROM unified_interactions
WHERE source = 'claude' AND timestamp > '2025-12-20';
```

### gf3_flow_analysis
Daily GF(3) balance tracking:
```sql
SELECT day, total_interactions, daily_gf3_sum, gf3_status, breakdown
FROM gf3_flow_analysis
WHERE gf3_status = '✓ balanced';
```

### gf3_momentum_detector
Hourly drift detection with velocity:
```sql
SELECT hour, cumulative_gf3, gf3_velocity_6h, momentum_status
FROM gf3_momentum_detector
WHERE momentum_status LIKE '%DRIFT%';
```

### fingerprint_correlations
Cross-source co-occurrence within 1-hour windows:
```sql
SELECT edge_type, correlation_count, avg_time_delta
FROM fingerprint_correlations
ORDER BY correlation_count DESC;
```

### interaction_velocity
Hourly momentum with cumulative GF(3):
```sql
SELECT hour, interactions, velocity, cumulative_gf3
FROM interaction_velocity
WHERE velocity > 20;  -- High activity spikes
```

### simultaneity_surfaces
High-density interaction periods:
```sql
SELECT hour_bucket, density, gf3_sum, gf3_status, palette
FROM simultaneity_surfaces;
```

## Capabilities

### 1. ingest-claude-history

```sql
CREATE OR REPLACE TABLE claude_history AS 
SELECT 
    display, timestamp,
    to_timestamp(timestamp/1000) as ts,
    project, sessionId,
    CASE 
        WHEN LOWER(display) LIKE '%duckdb%' THEN 'duckdb'
        WHEN LOWER(display) LIKE '%skill%' THEN 'skill'
        ELSE 'other'
    END as interaction_type
FROM read_json('~/.claude/history.jsonl', 
    format='newline_delimited',
    ignore_errors=true
);
```

### 2. apply-gay-coloring

```sql
-- Add Gay.jl deterministic coloring
CREATE OR REPLACE TABLE claude_history_colored AS
SELECT 
    *,
    hash(display || COALESCE(project,'') || CAST(timestamp AS VARCHAR)) as fingerprint,
    '#' || printf('%06x', ABS(hash(display)) % 16777216) as color_hex,
    CAST(ABS(hash(display)) % 3 AS INTEGER) - 1 as trit
FROM claude_history;
```

### 3. topic-extraction

```sql
-- Content-based topic clustering via regex
CREATE OR REPLACE TABLE topic_clusters AS
WITH topics AS (
    SELECT 
        content, source,
        CASE
            WHEN LOWER(content) LIKE '%duckdb%' THEN 'duckdb'
            WHEN LOWER(content) LIKE '%gay%' OR LOWER(content) LIKE '%color%' THEN 'gay-coloring'
            WHEN LOWER(content) LIKE '%acset%' THEN 'acsets'
            WHEN LOWER(content) LIKE '%skill%' THEN 'skills'
            WHEN LOWER(content) LIKE '%mcp%' THEN 'mcp'
            ELSE 'general'
        END as topic,
        trit, color_hex, timestamp
    FROM unified_interactions
)
SELECT 
    topic, COUNT(*) as mentions,
    SUM(trit) as gf3_sum,
    CASE WHEN SUM(trit) % 3 = 0 THEN '✓' ELSE '⚠' END as balanced,
    MIN(timestamp) as first_seen,
    MAX(timestamp) as last_seen
FROM topics
GROUP BY topic
ORDER BY mentions DESC;
```

### 4. momentum-detection

```sql
-- GF(3) momentum with 6h/24h velocity windows
CREATE OR REPLACE VIEW gf3_momentum_detector AS
WITH cumulative AS (
    SELECT 
        DATE_TRUNC('hour', timestamp) as hour,
        SUM(trit) as hourly_trit,
        SUM(SUM(trit)) OVER (ORDER BY DATE_TRUNC('hour', timestamp)) as cumulative_gf3
    FROM unified_interactions
    WHERE timestamp IS NOT NULL
    GROUP BY 1
),
with_velocity AS (
    SELECT 
        *,
        cumulative_gf3 - LAG(cumulative_gf3, 6) OVER (ORDER BY hour) as gf3_velocity_6h,
        cumulative_gf3 - LAG(cumulative_gf3, 24) OVER (ORDER BY hour) as gf3_velocity_24h
    FROM cumulative
)
SELECT 
    hour, hourly_trit, cumulative_gf3,
    gf3_velocity_6h, gf3_velocity_24h,
    CASE 
        WHEN ABS(gf3_velocity_6h) > 15 THEN '🔴 HIGH DRIFT'
        WHEN ABS(gf3_velocity_6h) > 8 THEN '🟡 MODERATE DRIFT'  
        WHEN cumulative_gf3 % 3 = 0 THEN '🟢 BALANCED'
        ELSE '⚪ STABLE'
    END as momentum_status
FROM with_velocity
ORDER BY hour DESC;
```

### 5. parquet-export

```sql
-- Export to Parquet for external analysis
COPY (SELECT * FROM unified_interactions WHERE timestamp IS NOT NULL)
TO 'ducklake_data/parquet/unified_interactions.parquet' (FORMAT PARQUET);

COPY (SELECT * FROM gf3_flow_analysis)
TO 'ducklake_data/parquet/gf3_flow.parquet' (FORMAT PARQUET);

COPY (SELECT * FROM simultaneity_surfaces)
TO 'ducklake_data/parquet/simultaneity_surfaces.parquet' (FORMAT PARQUET);
```

## GF(3) Triad Integration

| Trit | Skill | Role |
|------|-------|------|
| -1 | duckdb-timetravel | Temporal versioning |
| 0 | gay-mcp | Color stream generation |
| +1 | **duckdb-ies** | Interactome analytics |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## Current Interactome Stats

```
Total Interactions: 1733
Sources: 4 (claude, github_repo, github_contrib, skill)
Global GF(3): 2 (⚠ drift)
Balanced Topics: duckdb, gay-coloring, acsets, crdt, mcp, world-modeling
```

## Topic Distribution

| Topic | Mentions | GF(3) | Status |
|-------|----------|-------|--------|
| general | 1359 | 27 | ✓ balanced |
| gay-coloring | 117 | -6 | ✓ balanced |
| duckdb | 74 | -3 | ✓ balanced |
| skills | 50 | 2 | ⚠ drift |
| world-modeling | 34 | -3 | ✓ balanced |
| mcp | 31 | -9 | ✓ balanced |
| acsets | 20 | 0 | ✓ balanced |

## Parquet Outputs

```
ducklake_data/parquet/
├── unified_interactions.parquet
├── gf3_flow.parquet
└── simultaneity_surfaces.parquet
```

## In-Memory One-Liners (Distilled from 50+ Historical Attempts)

These patterns were extracted from ~/.claude/history.jsonl — the most frequently reinvented DuckDB invocations across sessions.

### 1. history.jsonl → duckdb (self-analysis)

```bash
# Full history as queryable table (in-memory, no file created)
duckdb -c "
SELECT display, to_timestamp(timestamp/1000) as ts, project, sessionId
FROM read_json('~/.claude/history.jsonl', format='newline_delimited', ignore_errors=true)
ORDER BY timestamp DESC LIMIT 20;"

# Session frequency by project
duckdb -c "
SELECT project, COUNT(DISTINCT sessionId) as sessions, COUNT(*) as msgs,
  MIN(to_timestamp(timestamp/1000))::DATE as first, MAX(to_timestamp(timestamp/1000))::DATE as last
FROM read_json('~/.claude/history.jsonl', format='newline_delimited', ignore_errors=true)
GROUP BY project ORDER BY sessions DESC;"

# Keyword search across all sessions
duckdb -c "
SELECT display, to_timestamp(timestamp/1000) as ts, sessionId
FROM read_json('~/.claude/history.jsonl', format='newline_delimited', ignore_errors=true)
WHERE LOWER(display) LIKE '%KEYWORD%'
ORDER BY timestamp DESC;"

# Combined claude + codex history
duckdb -c "
WITH all_hist AS (
  SELECT *, 'claude' as source FROM read_json('~/.claude/history.jsonl', format='newline_delimited', ignore_errors=true)
  UNION ALL
  SELECT *, 'codex' as source FROM read_json('~/.codex/history.jsonl', format='newline_delimited', ignore_errors=true)
)
SELECT source, COUNT(*) as msgs, COUNT(DISTINCT sessionId) as sessions
FROM all_hist GROUP BY source;"
```

### 2. gh cli → json → duckdb

**IMPORTANT**: DuckDB can't read JSON arrays from `/dev/stdin`. Two fixes:
- Use `--jq '.[]'` to emit newline-delimited JSON (preferred for pipes)
- Or save to temp file first: `gh ... > /tmp/gh.json && duckdb -c "... FROM read_json_auto('/tmp/gh.json')"`

```bash
# Org-wide repo stats (--jq '.[]' converts array → NDJSON for stdin)
gh repo list ORGNAME --json name,stargazerCount,forkCount,updatedAt,primaryLanguage --limit 200 --jq '.[]' \
| duckdb -c "
SELECT name, stargazerCount as stars, forkCount as forks,
  primaryLanguage.name as lang, updatedAt::DATE as updated
FROM read_json_auto('/dev/stdin') ORDER BY stars DESC;"

# Repo commit history via GraphQL (--jq extracts the array)
gh api graphql -f query='
  query($owner:String!,$name:String!) {
    repository(owner:$owner,name:$name) {
      defaultBranchRef { target { ... on Commit {
        history(first:100) { nodes { committedDate message author { name email } } }
      }}}
    }
  }' -f owner=OWNER -f name=REPO \
  --jq '.data.repository.defaultBranchRef.target.history.nodes[]' \
| duckdb -c "
SELECT author.name, COUNT(*) as commits,
  MIN(committedDate)::DATE as first, MAX(committedDate)::DATE as last
FROM read_json_auto('/dev/stdin') GROUP BY 1 ORDER BY commits DESC;"

# PR review cadence (temp file approach for complex nested JSON)
gh pr list --repo OWNER/REPO --state all --json number,createdAt,closedAt,author,reviewDecision --limit 200 > /tmp/prs.json && \
duckdb -c "
SELECT author.login, COUNT(*) as prs,
  AVG(DATEDIFF('hour', createdAt::TIMESTAMP, closedAt::TIMESTAMP)) as avg_hours_to_close
FROM read_json_auto('/tmp/prs.json')
WHERE closedAt IS NOT NULL
GROUP BY 1 ORDER BY prs DESC;"

# Issue interaction entropy
gh issue list --repo OWNER/REPO --state all --json number,title,author,labels,createdAt,comments --limit 300 --jq '.[]' \
| duckdb -c "
SELECT author.login,
  COUNT(*) as issues,
  AVG(LIST_LENGTH(labels)) as avg_labels,
  AVG(comments) as avg_comments
FROM read_json_auto('/dev/stdin') GROUP BY 1 ORDER BY issues DESC;"
```

### 3. HuggingFace → duckdb

```bash
# Load HF dataset directly (parquet endpoint)
duckdb -c "
SELECT * FROM 'hf://datasets/DATASET_OWNER/DATASET_NAME/data/*.parquet' LIMIT 10;"

# HF CSV dataset
duckdb -c "
SELECT * FROM read_csv_auto('hf://datasets/OWNER/NAME/file.csv') LIMIT 10;"

# Example: kernel vuln dataset
duckdb -c "
SELECT commit_hash, vuln_type, severity, COUNT(*) OVER (PARTITION BY vuln_type) as type_count
FROM read_csv_auto('hf://datasets/pebblebed/kernel-vuln-dataset/vuln_commits_full.csv')
ORDER BY severity DESC LIMIT 20;"
```

### 4. ATTACH sqlite (beeper, imessage, any sqlite)

```bash
# Beeper + iMessage cross-query
duckdb -c "
ATTACH '$HOME/Library/Application Support/BeeperTexts/account.db' AS beeper (TYPE sqlite, READ_ONLY);
ATTACH '$HOME/Library/Messages/chat.db' AS imessage (TYPE sqlite, READ_ONLY);
SELECT name FROM sqlite_master WHERE type='table';"

# Any sqlite file inline
duckdb -c "
ATTACH '/path/to/any.db' AS src (TYPE sqlite, READ_ONLY);
SELECT * FROM src.table_name LIMIT 10;"
```

### 5. polars/nushell ↔ duckdb via nuworlds

```bash
# Nushell table → parquet → duckdb
nu -c 'ls | to parquet | save /tmp/ls.parquet'
duckdb -c "SELECT * FROM '/tmp/ls.parquet';"

# Nushell polars DataFrame → duckdb
nu -c '[[a b]; [1 2] [3 4]] | polars into-df | polars to-parquet /tmp/df.parquet'
duckdb -c "SELECT * FROM '/tmp/df.parquet';"

# duckdb → nushell via JSON
duckdb -json -c "SELECT * FROM read_json('~/.claude/history.jsonl', format='newline_delimited', ignore_errors=true) LIMIT 5" | nu -c '$in | from json'
```

### 6. llms.txt → duckdb structured decomposition

```bash
# Fetch and structure llms.txt
curl -sL https://DOMAIN/llms.txt | duckdb -c "
WITH lines AS (
  SELECT unnest(string_split(content, chr(10))) as line,
    generate_series as line_no
  FROM (SELECT read_text('/dev/stdin') as content)
  CROSS JOIN generate_series(1, 10000)
)
SELECT line_no, line FROM lines WHERE line != '' LIMIT 50;"

# Or via babashka for richer parsing
bb -e '(require (quote [babashka.http-client :as http]) (quote [cheshire.core :as json]))
(let [txt (:body (http/get "https://DOMAIN/llms.txt"))
      lines (clojure.string/split-lines txt)]
  (println (json/generate-string (map-indexed (fn [i l] {:line_no i :text l :section (when (re-find #"^#" l) l)}) lines))))' \
| duckdb -c "SELECT section, COUNT(*) as lines FROM read_json('/dev/stdin') WHERE section IS NOT NULL GROUP BY 1;"
```

### 7. duckdb VSS (vector similarity search)

```bash
# Install and use VSS extension
duckdb -c "
INSTALL vss; LOAD vss;
CREATE TABLE embeddings (id INT, vec FLOAT[384]);
-- Insert embeddings, then:
SELECT id, array_cosine_similarity(vec, ?::FLOAT[384]) as sim
FROM embeddings ORDER BY sim DESC LIMIT 10;"
```

### 8. Babashka + duckdb (bb one-liners)

```bash
# Babashka → duckdb pipeline
bb -e '(-> (babashka.process/shell {:out :string} "duckdb" "-json" "-c"
  "SELECT display, project FROM read_json_auto('"'"'~/.claude/history.jsonl'"'"') WHERE display LIKE '"'"'%duckdb%'"'"' ORDER BY timestamp DESC LIMIT 5")
  :out (cheshire.core/parse-string true))'

# Find all .duckdb files on system
bb -e '(run! println (babashka.fs/glob "." "**/*.duckdb"))'
```

## CLI Recipes

```bash
# Quick interactome status
duckdb /Users/bob/ies/ducklake_data/ies_interactome.duckdb -c "
SELECT source, COUNT(*), SUM(trit) as gf3 FROM unified_interactions GROUP BY source;"

# Check momentum drift
duckdb /Users/bob/ies/ducklake_data/ies_interactome.duckdb -c "
SELECT * FROM gf3_momentum_detector WHERE momentum_status LIKE '%DRIFT%' LIMIT 10;"

# Topic balance check
duckdb /Users/bob/ies/ducklake_data/ies_interactome.duckdb -c "
SELECT topic, mentions, gf3_sum, balanced FROM topic_clusters ORDER BY mentions DESC;"

# Recent high-density hours
duckdb /Users/bob/ies/ducklake_data/ies_interactome.duckdb -c "
SELECT * FROM simultaneity_surfaces ORDER BY density DESC LIMIT 5;"
```

## Related Skills

- `duckdb-timetravel` - Temporal versioning layer
- `gay-mcp` - Deterministic color generation
- `acsets` - Category-theoretic schema
- `entropy-sequencer` - Temporal arrangement
- `bisimulation-game` - Cross-agent skill dispersal



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Dataframes
- **polars** [○] via bicomodule
  - High-performance dataframes

### Bibliography References

- `general`: 734 citations in bib.duckdb



## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 10. Adventure Game Example

**Concepts**: autonomous agent, game, synthesis

### GF(3) Balanced Triad

```
duckdb-ies (−) + SDF.Ch10 (+) + [balancer] (○) = 0
```

**Skill Trit**: -1 (MINUS - verification)

### Secondary Chapters

- Ch6: Layering

### Connection Pattern

Adventure games synthesize techniques. This skill integrates multiple patterns.
## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.

## Forward Reference

- unified-reafference (IES session unification)