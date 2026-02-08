---
name: duckdb-temporal-versioning
description: Temporal versioning and interaction history with time-travel queries,
model: inherit
tools: ["Read", "Edit", "Execute", "WebSearch"]
---

<!-- Propagated to amp | Trit: +1 | Source: .ruler/skills/duckdb-temporal-versioning -->

# DuckDB Temporal Versioning Skill

**Status**: ✅ Production Ready
**Trit**: +1 (PLUS - generative/creating databases)
**Principle**: Same data → Same structure (SPI guarantee)
**Implementation**: DuckDB (embedded SQL) + Temporal semantics
**GF(3) Balanced Triad**:
- duckdb-temporal-versioning (+1) [Generator: Create/write]
- clj-kondo-3color (-1) [Validator: Verify schemas]
- acsets (0) [Coordinator: Navigate relationships]

---

## Overview

**DuckDB Temporal Versioning** provides in-process SQL database with time-travel semantics for storing and analyzing interaction history. Every database with the same schema and initial data produces identical query results, enabling:

1. **Time Travel**: Query data as of any past transaction
2. **Deterministic Replay**: Freeze snapshots for reproducible execution
3. **Causality Tracking**: Track dependencies via vector clocks
4. **Immutable Audit Logs**: Record all mutations permanently
5. **Multi-Layer Integration**: Combine history + world databases + derived views

## Core Capabilities

### Time-Travel Semantics

```sql
-- Query data as of transaction T₁
SELECT * FROM interactions
VERSION AT SYSTEM_TIME AS OF T₁;

-- Get all versions of a row
SELECT *, transaction_id
FROM interactions
FOR SYSTEM_TIME ALL
WHERE id = 42;
```

### Causality Tracking with Vector Clocks

```sql
-- Track causal relationships
CREATE TABLE causality_log (
  event_id INTEGER,
  vector_clock VARCHAR,    -- e.g., "[1, 2, 3, 0]"
  event_data STRUCT,
  timestamp TIMESTAMP,
  UNIQUE(vector_clock)
);

-- Query causality constraints
SELECT * FROM causality_log
WHERE vector_clock <= '[2, 3, 1, 1]'
ORDER BY vector_clock;
```

### Frozen Snapshots for Determinism

```sql
-- Create checkpoint
PRAGMA freeze_table('interactions');

-- Later: All queries return identical results
SELECT COUNT(*) FROM interactions;  -- Always same value

-- Unfreeze to add new data
PRAGMA unf