---
name: duckdb-ies
description: ' Layer 4: IES Interactome Analytics with GF(3) Momentum Tracking'
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
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
SELECT hour, interactions