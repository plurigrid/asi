# DuckLake Cognition Skill

Ingest Claude/Amp thread history into DuckLake with ACSet mutual awareness graph and GF(3) coloring.

## Overview

Transforms 1000s of Claude conversation files into a queryable cognition database with:
- Temporal indexing across epochs
- Play/coplay awareness edges between sessions
- GF(3) trit coloring for triadic balance
- WEV (World Extractable Value) bridge to Aptos

## Files

| File | Purpose |
|------|---------|
| `ingest.py` | Ingest Claude .jsonl files into DuckLake |
| `wev_bridge.bb` | Connect cognition to Aptos settlement |
| `schema.sql` | DuckDB schema for cognition tables |

## Usage

```bash
# One-time ingestion
uv run --with duckdb python ~/.claude/skills/ducklake-cognition/ingest.py

# Run WEV extraction
bb ~/.claude/skills/ducklake-cognition/wev_bridge.bb

# Query cognition
duckdb ~/worldnet/cognition.duckdb "SELECT * FROM sessions LIMIT 5"
```

## Schema

### Tables

- **messages**: Individual messages with content, timestamps, GF(3) trits
- **sessions**: Session metadata and project paths
- **awareness_edges**: Play/coplay/fork edges between sessions
- **temporal_index**: Time-ordered message flow by epoch
- **trit_ledger**: GF(3) conservation verification

### Awareness Edge Types

| Type | Meaning |
|------|---------|
| `fork` | Sessions from same project directory |
| `play` | Temporal overlap (same hour) |
| `coplay` | Inverse of play (bidirectional) |
| `reference` | Explicit cross-reference |

## GF(3) Conservation

Every operation maintains: `Σ trits ≡ 0 (mod 3)`

```sql
SELECT SUM(trit) % 3 as conserved FROM messages;
-- Should return 0
```

## Integration with Active Interleave

Use with `active-interleave` skill for random walks through recent cognition:

```bash
bb ~/.claude/skills/active-interleave/active.bb --hours 6
```

## WEV Bridge

Connects cognition metrics to Aptos settlement:

```
MINUS (-1): Validate cognition state
ERGODIC (0): Compute WEV metrics  
PLUS (+1): Generate settlement intent
```

Output:
```clojure
{:target-world :world-a
 :wev 1.0
 :apt-amount 0.001
 :ready true}
```
