# DuckDB Best Practices & SKILL Recommendation

**Status**: Research Complete
**Date**: 2025-12-21
**Finding**: No existing DuckDB SKILL.md, but comprehensive best practices documented

---

## Executive Summary

### DuckDB Usage in Project
- **23 unique sessions** with 454 DuckDB references in history
- **5 major database files** with specific purposes (exa_research, music_knowledge, moebius_coinflip, provenance)
- **Comprehensive best practices** documented in 4 major files
- **5 SQL schema files** defining databases
- **NO dedicated SKILL.md** for DuckDB operations

### Recommendation
**CREATE: DuckDB skill as part of Phase 4** to formalize best practices and enable systematic usage.

---

## Best Practices Found in Existing Documentation

### 1. Performance Optimization (from DUCKDB_GRAPHQL_DEPLOYMENT.md)

**Buffer Management**:
```sql
-- Set buffer pool for large datasets
PRAGMA threads = 4;
PRAGMA memory_limit = '8GB';
PRAGMA default_order = 'ASC NULLS LAST';
```

**Compression Strategy**:
```sql
-- Use SNAPPY for typical workloads
CREATE TABLE data (
  id INTEGER,
  value VARCHAR,
  created_at TIMESTAMP
) WITH (compression='snappy');
```

**Materialized Views for Performance**:
```sql
-- Cache expensive queries
CREATE MATERIALIZED VIEW stats AS
SELECT
  DATE(timestamp) as date,
  COUNT(*) as count,
  AVG(value) as avg_value
FROM raw_data
GROUP BY DATE(timestamp);
```

**Connection Pooling**:
```python
# Use QueuePool for multiple connections
from sqlalchemy import create_engine
from sqlalchemy.pool import QueuePool

engine = create_engine(
    'duckdb:///db.duckdb',
    poolclass=QueuePool,
    pool_size=5,
    max_overflow=10
)
```

---

### 2. Temporal Features (from DUCKDB_THREADS_ANALYSIS.md)

**Time Travel Semantics**:
```sql
-- Use transaction IDs for time travel
BEGIN TRANSACTION;
  INSERT INTO events (id, data) VALUES (1, 'event1');
COMMIT;  -- Transaction ID = T1

-- Later: Query as of transaction T1
SELECT * FROM events VERSION AT SYSTEM_TIME AS OF T1;
```

**Frozen Snapshots for Replay**:
```sql
-- Create checkpoint/snapshot
PRAGMA freeze_table('events');

-- Enables deterministic replay
SELECT * FROM events;  -- Always returns same data
```

**Logical Clock for Simultaneity**:
```sql
-- Track causality with vector clocks
CREATE TABLE causality_log (
  event_id INTEGER,
  vector_clock VARCHAR,  -- e.g., "[1, 2, 3]"
  timestamp TIMESTAMP,
  UNIQUE(vector_clock)
);
```

---

### 3. Integration Patterns (from DUCKDB_KNOWLEDGE_GRAPH_SCHEMA.sql)

**Multi-Layer Query Strategy**:
```sql
-- Layer 1: History queries (fast, indexed)
SELECT * FROM claude_history
WHERE session_id IN (...)

-- Layer 2: World databases (transformed)
SELECT * FROM interaction_features
WHERE interaction_id IN (...)

-- Layer 3: Integration (unified view)
SELECT h.*, w.features
FROM claude_history h
JOIN interaction_features w ON h.interaction_id = w.interaction_id
```

**Refinement Query Pattern** (broad → trifurcated → refined):
```sql
-- Stage 1: Broad query
SELECT COUNT(*) FROM all_interactions;  -- 10,000 records

-- Stage 2: Trifurcated (split into 3)
SELECT type, COUNT(*)
FROM all_interactions
GROUP BY type;

-- Stage 3: Refined
SELECT * FROM all_interactions
WHERE type = 'technical-innovation'
AND confidence > 0.8
AND date BETWEEN '2025-12-01' AND '2025-12-21'
LIMIT 100;
```

---

### 4. Audit & Monitoring (from db/migrations/)

**Immutable Audit Logs**:
```sql
-- Create audit trigger
CREATE TRIGGER audit_insert_events
AFTER INSERT ON events
FOR EACH ROW
BEGIN
  INSERT INTO audit_log (
    table_name, operation, old_value, new_value, timestamp
  ) VALUES (
    'events', 'INSERT', NULL, NEW, NOW()
  );
END;
```

**Statistics Views**:
```sql
-- Create monitoring view
CREATE VIEW operation_stats AS
SELECT
  table_name,
  operation,
  COUNT(*) as count,
  MIN(timestamp) as first_op,
  MAX(timestamp) as last_op
FROM audit_log
GROUP BY table_name, operation;
```

**CSV/JSON Export for Analysis**:
```sql
-- Export to CSV
COPY operation_stats TO 'stats.csv' WITH (FORMAT CSV);

-- Export to JSON
COPY operation_stats TO 'stats.json' WITH (FORMAT JSON);
```

---

### 5. Backup & Recovery (from DUCKDB_GRAPHQL_DEPLOYMENT.md)

**Backup Procedures**:
```bash
# Full backup
duckdb db.duckdb ".backup backup.db"

# Incremental backup (copy file)
cp db.duckdb db.duckdb.backup.$(date +%Y%m%d)

# Verify integrity
duckdb db.duckdb "PRAGMA integrity_check;"
```

**Recovery from Backups**:
```bash
# Restore from backup
duckdb db.duckdb ".restore backup.db"

# Verify restoration
duckdb backup.db "SELECT COUNT(*) FROM events;"
```

---

## DuckDB Skill Recommendation

### Why Create a DuckDB SKILL?

**Current State**:
- 23 unique sessions reference DuckDB operations
- 5 database files with different schemas
- Best practices scattered across 4 documentation files
- No unified skill definition for systematic usage

**Benefits of Creating SKILL**:
1. **Centralized best practices** in one location
2. **GF(3)-balanced triadic loading** with validator/coordinator/generator roles
3. **Reusable across projects** beyond music-topos
4. **Integration with Phase 4** tree-sitter MCP + agent training
5. **Documented patterns** for time travel, audit, recovery

---

### Proposed DuckDB SKILL.md

```yaml
# DuckDB SKILL Definition

name: duckdb-temporal-versioning
category: Database & Temporal Systems
polarity: [+1]  # Generator role (create databases, write data)
alias_polarities:
  validator: clj-kondo-3color  # Validate schema/integrity
  coordinator: acsets  # Navigate schema relationships

description: |
  Temporal versioning and provenance database for interaction history.
  Enables time-travel semantics, deterministic replay, and causality tracking.

use_cases:
  - Store interaction history with causal ordering
  - Enable time-travel queries (as-of specific transactions)
  - Track audit logs with immutable semantics
  - Analyze causality via vector clocks
  - Export data for external analysis (CSV/JSON)

core_operations:
  - create_database: Initialize new DuckDB with schema
  - insert_events: Add interactions with causality tracking
  - query_as_of: Time-travel queries to specific point
  - freeze_snapshot: Create checkpoint for deterministic replay
  - audit_log_export: Export changes for analysis
  - backup_restore: Manage database persistence

best_practices:
  performance:
    - Use SNAPPY compression for storage
    - Set memory_limit to 8GB for typical workloads
    - Create materialized views for expensive aggregations
    - Use QueuePool for concurrent connections
    - Index frequently-queried columns

  temporal:
    - Track vector clocks for causality
    - Use transaction IDs for time-travel queries
    - Create frozen snapshots for deterministic replay
    - Maintain immutable audit logs

  integration:
    - Use multi-layer query strategy (history → world → unified)
    - Apply refinement pattern (broad → trifurcated → refined)
    - Export via CSV/JSON for analysis
    - Validate with PRAGMA integrity_check

examples:
  - Music-topos: Track @barton's interactions with causality
  - Agent-o-rama: Store training traces with time-travel capability
  - Network analysis: Query interaction relationships at any point in time
  - Provenance: Maintain immutable audit trail of all changes

documentation:
  - DUCKDB_GRAPHQL_DEPLOYMENT.md (565 lines)
  - DUCKDB_THREADS_ANALYSIS.md (410 lines)
  - DUCKDB_KNOWLEDGE_GRAPH_SCHEMA.sql
  - db/migrations/* (various schema files)
```

---

## Integration with Phase 4

### DuckDB Role in Agent Training

**Phase 4 Uses DuckDB For**:
1. **Trace Storage**: Training iterations → DuckDB
2. **History Queries**: Analyze prior training runs
3. **Time-Travel**: Revert to best checkpoint
4. **Audit Logs**: Track all agent decisions
5. **Provenance**: Map data lineage

**GF(3) Skill Coordination**:
```
duckdb-temporal-versioning (+1)  [Generator: Create databases]
   ⊗ clj-kondo-3color (-1)        [Validator: Check schema/integrity]
   ⊗ acsets (0)                   [Coordinator: Navigate relationships]
   = 0 (mod 3) ✓
```

---

## Files with DuckDB Best Practices

### Documentation
1. **DUCKDB_GRAPHQL_DEPLOYMENT.md** (565 lines)
   - Performance tuning strategies
   - Connection pooling
   - Backup/restore procedures
   - Monitoring & maintenance

2. **DUCKDB_THREADS_ANALYSIS.md** (410 lines)
   - 23 unique session patterns
   - Time travel semantics
   - Multi-agent coordination
   - Causality tracking

3. **EXA_RESEARCH_DUCKDB_GUIDE.md** (470 lines)
   - Research task history
   - Analysis queries
   - Cost tracking
   - Performance characteristics

4. **JUSTFILE_MONAD_DUCKDB_SYNTHESIS.md** (560 lines)
   - Provenance logic
   - GraphQL integration
   - Natural transformations

### SQL Schemas
1. **DUCKDB_KNOWLEDGE_GRAPH_SCHEMA.sql** (415 lines)
   - Content indexing (13 tables, 5 views, 11 indices)
   - Recursive learning paths
   - Multi-layer query patterns

2. **db/migrations/*** (various)
   - CRDT memoization schema
   - ACSet history views
   - Thread operad structures
   - Provenance tracking

---

## Action Items

### Immediate (This Week)
- [ ] Review DUCKDB_GRAPHQL_DEPLOYMENT.md (performance tuning)
- [ ] Review DUCKDB_THREADS_ANALYSIS.md (time travel patterns)
- [ ] Understand multi-layer query strategy

### For Phase 4 Implementation
- [ ] Create DuckDB SKILL.md in .agents/skills/duckdb-temporal-versioning/
- [ ] Implement as GF(3) balanced triad:
  - Generator (+1): duckdb-temporal-versioning (create/write)
  - Validator (-1): clj-kondo-3color (verify schema)
  - Coordinator (0): acsets (navigate relationships)
- [ ] Add trace storage to agent-o-rama module
- [ ] Implement time-travel checkpoint restoration

### For Future Use
- [ ] Create duckdb-query-builder skill (refine pattern)
- [ ] Add real-time audit log streaming
- [ ] Build graphql-duckdb bridge for exploration

---

## Summary: Best Practices by Category

### Performance (Most Important)
1. Set memory_limit = '8GB'
2. Use SNAPPY compression
3. Create materialized views for aggregations
4. Use QueuePool for concurrent access
5. Index frequently-queried columns

### Temporal (For Phase 4)
1. Track vector clocks for causality
2. Use transaction IDs for time-travel
3. Create frozen snapshots for replay
4. Maintain immutable audit logs
5. Enable PRAGMA freeze_table

### Integration (For Multi-Agent)
1. Use multi-layer query strategy
2. Apply refinement pattern (broad → trifurcated → refined)
3. Export via CSV/JSON for analysis
4. Validate with PRAGMA integrity_check
5. Maintain backup/restore procedures

---

## Conclusion

**No DuckDB SKILL.md exists yet**, but comprehensive best practices are documented across multiple files.

**Recommendation**: Create `duckdb-temporal-versioning` SKILL for Phase 4, balanced with `clj-kondo-3color` (validator) and `acsets` (coordinator) in GF(3) triad.

**Priority**: Medium-High (important for trace storage in agent training, but not blocking Phase 4 start).

---

Generated: 2025-12-21
Status: Research Complete
Next: Create DuckDB SKILL.md for Phase 4 Integration
