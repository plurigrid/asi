---
name: ducklake-walk
description: Ergodic random walks over DuckLake lakehouses with GF(3) triadic concurrent walkers. Society-of-mind coordination for schema exploration.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# DuckLake Random Walk

Ergodic random walk exploration of DuckDB/DuckLake schemas with concurrent Society-of-Mind walkers. Implements PageRank-style teleportation for irreducibility and GF(3)-balanced walker coordination.

## Triadic Structure

| Stream | Trit | Role | Implementation |
|--------|------|------|----------------|
| MINUS (-1) | Validator | Constraint verification, DuckLake semantics | `duckdb-validator.sql` |
| ERGODIC (0) | Coordinator | Random walk orchestration | `ducklake-walk.clj` |
| PLUS (+1) | Generator | Concurrent walker execution | `mensi_walker.py` |

**Conservation**: Σ trits = -1 + 0 + 1 = 0 (mod 3) ✓

## Lojban Gismu Mapping

| Gismu | Meaning | Component |
|-------|---------|-----------|
| pensi | think | `PensiWalker` - individual cognition |
| jimpe | understand | `Jimpe` - shared understanding |
| djuno | know | `Djuno` - knowledge units |
| mensi | sibling | Walker siblings in society |
| gunma | group | `GunmaSociety` - collective |

## Algorithm: Ergodic Random Walk

The walk follows a Markov chain with teleportation (PageRank-style):

```
P(teleport) = 0.15  # Random restart for ergodicity
P(follow_edge) = 0.85 × (has_neighbors ? 1 : 0)
P(forced_teleport) = 1 - P(teleport) - P(follow_edge)
```

**Guarantees**:
- **Irreducibility**: All tables reachable via teleportation
- **Aperiodicity**: Random restarts break cycles
- **Ergodicity**: Unique stationary distribution exists

## Usage

### Babashka Ergodic Walker (ERGODIC stream)

```bash
# Demo mode with in-memory schema
bb ducklake-walk.clj

# With existing DuckDB file
bb ducklake-walk.clj /path/to/lakehouse.duckdb
```

### Python Society-of-Mind (PLUS stream)

```bash
# Run concurrent walkers
python mensi_walker.py

# Interactive REPL
python jimpe_repl.py
```

### DuckLake Validation (MINUS stream)

```sql
LOAD ducklake;
ATTACH 'ducklake:metadata.duckdb' AS lake (DATA_PATH './data');

-- Create walk history table
CREATE TABLE lake.main.walk_history (
    step_id INTEGER,
    fr