---
name: hyjax-relational
description: HyJAX Relational Thinking Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# HyJAX Relational Thinking Skill

Apply relational thinking (ACSets/C-Sets) to Amp thread analysis using HyJAX patterns.

## When to Use

- Analyzing thread relationships and concept networks
- Extracting patterns from conversation history
- Building relational databases from unstructured thread data
- Generating Colored S-expressions for visualization

## Core Concepts

### ACSet Schema for Threads
```
Objects: Thread, Message, Concept, File
Morphisms: thread_msg, mentions, discusses, related
Attributes: content, timestamp, info_gain
```

### Colored S-expressions
```lisp
(acset-gold
  (threads-red (thread T-001 "Title" 42))
  (concepts-green (concept skill 5) (concept MCP 3))
  (relations-purple (edge skill co-occurs subagent)))
```

## Key Files

| File | Purpose |
|------|---------|
| `/Users/bob/ies/music-topos/lib/thread_relational_hyjax.hy` | Main HyJAX analyzer |
| `/Users/bob/ies/music-topos/lib/unified_thread_lake.duckdb` | Persistent database |
| `/Users/bob/ies/music-topos/lib/analyze_threads_relational.py` | Python analyzer |

## Quick Start

### 1. Query the Thread Lake
```bash
duckdb /Users/bob/ies/music-topos/lib/unified_thread_lake.duckdb -c "
  SELECT name, hub_score FROM concepts ORDER BY hub_score DESC LIMIT 10
"
```

### 2. Find 2-Hop Concept Paths
```bash
duckdb /Users/bob/ies/music-topos/lib/unified_thread_lake.duckdb -c "
  SELECT r1.from_concept || ' → ' || r1.to_concept || ' → ' || r2.to_concept as path
  FROM concept_relations r1
  JOIN concept_relations r2 ON r1.to_concept = r2.from_concept
  WHERE r1.from_concept = 'skill'
"
```

### 3. Run Full Analysis
```bash
cd /Users/bob/ies && source .venv/bin/activate
python3 music-topos/lib/full_thread_analysis.py
```

## Relational Patterns

### Hub Concepts (Most Connected)
| Concept | Hub Score |
|---------|-----------|
| skill | 8 |
| GF3 | 5 |
| MCP | 4 |
| subagent | 3 |

### Strongest Relations
- skill ↔ subagent (weight 2)
- skill → MCP → alife
- skill → ACSet → discohy
- HyJAX ↔ relatio