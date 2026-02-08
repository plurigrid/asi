---
name: duckdb-temporal-versioning
description: Temporal versioning and interaction history with time-travel queries, causality tracking, and deterministic replay
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
PRAGMA unfreeze_table('interactions');
```

### Immutable Audit Logs (3-Trigger Pattern)

```sql
-- Trigger on INSERT
CREATE TRIGGER audit_insert_interactions
AFTER INSERT ON interactions
FOR EACH ROW
BEGIN
  INSERT INTO audit_log (
    table_name, operation, record_id, new_value, timestamp
  ) VALUES (
    'interactions', 'INSERT', NEW.id, NEW, NOW()
  );
END;

-- Trigger on UPDATE
CREATE TRIGGER audit_update_interactions
AFTER UPDATE ON interactions
FOR EACH ROW
BEGIN
  INSERT INTO audit_log (
    table_name, operation, record_id, old_value, new_value, timestamp
  ) VALUES (
    'interactions', 'UPDATE', NEW.id, OLD, NEW, NOW()
  );
END;

-- Trigger on DELETE
CREATE TRIGGER audit_delete_interactions
AFTER DELETE ON interactions
FOR EACH ROW
BEGIN
  INSERT INTO audit_log (
    table_name, operation, record_id, old_value, timestamp
  ) VALUES (
    'interactions', 'DELETE', OLD.id, OLD, NOW()
  );
END;
```

## Performance Optimization

### Buffer & Memory Management

```sql
-- Set buffer pool
PRAGMA threads = 4;
PRAGMA memory_limit = '8GB';

-- Check current memory
PRAGMA database_size;
```

### Compression Strategy

```sql
-- Use SNAPPY compression (good for typical workloads)
CREATE TABLE interactions (
  id INTEGER,
  user_id VARCHAR,
  content VARCHAR,
  created_at TIMESTAMP,
  vector_clock VARCHAR
) WITH (compression='snappy');
```

### Materialized Views for Expensive Queries

```sql
-- Cache aggregations
CREATE MATERIALIZED VIEW interaction_stats AS
SELECT
  DATE(created_at) as date,
  COUNT(*) as count,
  COUNT(DISTINCT user_id) as unique_users,
  AVG(LENGTH(content)) as avg_content_length
FROM interactions
GROUP BY DATE(created_at);

-- Query cache instead of raw table
SELECT * FROM interaction_stats WHERE date >= '2025-12-20';
```

### Connection Pooling (Python)

```python
from sqlalchemy import create_engine
from sqlalchemy.pool import QueuePool

# Use connection pool for concurrent access
engine = create_engine(
    'duckdb:////Users/bob/ies/music-topos/db.duckdb',
    poolclass=QueuePool,
    pool_size=5,
    max_overflow=10,
    pool_recycle=3600
)

# Connections reused efficiently
with engine.connect() as conn:
    result = conn.execute("SELECT COUNT(*) FROM interactions")
```

## Multi-Layer Query Strategy

### Layer 1: History Queries (Fast)

```sql
-- Indexed queries on interaction history
SELECT * FROM interactions
WHERE user_id IN ('alice', 'bob')
  AND created_at > '2025-12-20'
LIMIT 100;
```

### Layer 2: World Transformations

```sql
-- Feature extraction from raw interactions
SELECT
  id,
  user_id,
  EXTRACT(HOUR FROM created_at) as hour_of_day,
  LENGTH(content) as content_length,
  (SELECT COUNT(*) FROM interactions i2
   WHERE i2.user_id = i1.user_id) as user_interaction_count
FROM interactions i1;
```

### Layer 3: Unified Integration View

```sql
-- Join history + world databases
SELECT
  h.id,
  h.user_id,
  h.content,
  h.created_at,
  w.hour_of_day,
  w.content_length,
  w.user_interaction_count
FROM interactions h
JOIN interaction_features w ON h.id = w.id
WHERE h.created_at >= '2025-12-20'
ORDER BY h.created_at DESC;
```

## Refinement Query Pattern

```sql
-- Stage 1: BROAD query (understand scale)
SELECT COUNT(*) as total_interactions
FROM interactions;
-- Result: 10,000

-- Stage 2: TRIFURCATED (split into 3)
SELECT
  'technical-innovation' as pattern,
  COUNT(*) as count,
  AVG(content_length) as avg_length
FROM interactions
WHERE content LIKE '%algorithm%' OR content LIKE '%optimization%'
UNION ALL
SELECT
  'collaborative-work' as pattern,
  COUNT(*) as count,
  AVG(content_length) as avg_length
FROM interactions
WHERE content LIKE '%team%' OR content LIKE '%coordination%'
UNION ALL
SELECT
  'other' as pattern,
  COUNT(*) as count,
  AVG(content_length) as avg_length
FROM interactions
WHERE content NOT LIKE '%algorithm%'
  AND content NOT LIKE '%team%';

-- Stage 3: REFINED (focus on interesting subset)
SELECT *
FROM interactions
WHERE content LIKE '%algorithm%'
  AND content_length > 100
  AND user_id NOT IN (SELECT id FROM bots)
ORDER BY created_at DESC
LIMIT 50;
```

## Backup & Recovery

### Full Backup

```bash
# Create backup
duckdb /Users/bob/ies/music-topos/db.duckdb \
  ".backup /Users/bob/ies/music-topos/db.duckdb.backup"

# Verify backup size
ls -lh /Users/bob/ies/music-topos/db.duckdb*
```

### Incremental Backup (Copy Strategy)

```bash
# Copy database file with timestamp
cp /Users/bob/ies/music-topos/db.duckdb \
   /Users/bob/ies/music-topos/db.duckdb.backup.$(date +%Y%m%d_%H%M%S)

# Keep last 7 backups
ls -t /Users/bob/ies/music-topos/db.duckdb.backup.* | \
  tail -n +8 | \
  xargs rm -f
```

### Integrity Check

```bash
# Verify database integrity
duckdb /Users/bob/ies/music-topos/db.duckdb \
  "PRAGMA integrity_check;"
```

### Restore from Backup

```bash
# Restore from backup
duckdb /Users/bob/ies/music-topos/db.duckdb \
  ".restore /Users/bob/ies/music-topos/db.duckdb.backup"

# Verify restoration
duckdb /Users/bob/ies/music-topos/db.duckdb.backup \
  "SELECT COUNT(*) FROM interactions;"
```

## Data Export for Analysis

### Export to CSV

```sql
-- Export all interactions
COPY interactions TO '/tmp/interactions.csv' WITH (FORMAT CSV);

-- Export with header
COPY interactions TO '/tmp/interactions.csv'
WITH (FORMAT CSV, HEADER TRUE);

-- Export filtered subset
COPY (
  SELECT id, user_id, content_length, created_at
  FROM interactions
  WHERE created_at >= '2025-12-20'
) TO '/tmp/recent_interactions.csv'
WITH (FORMAT CSV, HEADER TRUE);
```

### Export to JSON

```sql
-- Export to JSON
COPY interactions TO '/tmp/interactions.json' WITH (FORMAT JSON);

-- Export nested structure
COPY (
  SELECT
    id,
    user_id,
    content,
    created_at,
    struct_pack(
      vector_clock := vector_clock,
      transaction_id := transaction_id
    ) as metadata
  FROM interactions
) TO '/tmp/interactions_with_metadata.json'
WITH (FORMAT JSON);
```

### Export to Parquet

```sql
-- Export to Parquet (columnar, efficient)
COPY interactions TO '/tmp/interactions.parquet'
WITH (FORMAT PARQUET);
```

## API: SQL Interface

### Python

```python
import duckdb

# Connect to database
conn = duckdb.connect('/Users/bob/ies/music-topos/db.duckdb')

# Execute query
result = conn.execute(
  "SELECT COUNT(*) FROM interactions"
).fetchall()

# Parameterized query (safe)
rows = conn.execute(
  "SELECT * FROM interactions WHERE user_id = ? LIMIT 10",
  ['alice']
).fetchdf()  # Returns pandas DataFrame

# Insert data
conn.execute(
  "INSERT INTO interactions (user_id, content, created_at) VALUES (?, ?, ?)",
  ['bob', 'Hello world', '2025-12-21 10:00:00']
)

conn.close()
```

### Clojure

```clojure
(require '[duckdb.core :as db])

;; Connect
(def conn (db/connect "db.duckdb"))

;; Query
(db/query conn "SELECT COUNT(*) FROM interactions")

;; Insert
(db/execute! conn
  "INSERT INTO interactions (user_id, content) VALUES (?, ?)"
  ["alice" "Hello"])

;; Time-travel query
(db/query conn
  "SELECT * FROM interactions VERSION AT SYSTEM_TIME AS OF ?1"
  [transaction-id])

;; Close
(db/close conn)
```

### Ruby

```ruby
require 'duckdb'

# Connect
db = DuckDB::Database.new('db.duckdb')

# Query
result = db.execute(
  "SELECT COUNT(*) FROM interactions"
)

# Insert
db.execute(
  "INSERT INTO interactions (user_id, content) VALUES (?, ?)",
  ['bob', 'Hello world']
)

# Parameterized
rows = db.execute(
  "SELECT * FROM interactions WHERE user_id = ?",
  ['alice']
)
```

## GF(3) Balanced Integration

### Triadic Skill Loading

```
duckdb-temporal-versioning (+1)
  Generator: Create/write databases
  - initialize_database: Set up schema
  - insert_events: Add interactions
  - snapshot_checkpoint: Freeze state

clj-kondo-3color (-1)
  Validator: Verify schemas
  - validate_schema: Check table definitions
  - integrity_check: PRAGMA integrity_check
  - audit_log_verify: Verify mutation log

acsets (0)
  Coordinator: Navigate relationships
  - query_relationships: Find foreign keys
  - walk_dependency_graph: Traverse schema
  - export_schema: Generate documentation
```

### Example: GF(3) Conservation

```clojure
;; Load balanced triad
(load-skills
  [:duckdb-temporal-versioning    ;; +1 (create)
   :clj-kondo-3color              ;; -1 (validate)
   :acsets])                       ;; 0 (coordinate)

;; GF(3) sum: (+1) + (-1) + (0) = 0 ✓
```

## Monitoring & Maintenance

### Statistics View

```sql
-- Create monitoring view
CREATE VIEW database_stats AS
SELECT
  COUNT(*) as total_records,
  COUNT(DISTINCT user_id) as unique_users,
  MIN(created_at) as oldest_record,
  MAX(created_at) as newest_record,
  DATEDIFF(DAY, MIN(created_at), MAX(created_at)) as days_spanned,
  AVG(LENGTH(content)) as avg_content_length
FROM interactions;

-- Query stats
SELECT * FROM database_stats;
```

### Audit Log Analysis

```sql
-- Track mutations
SELECT
  table_name,
  operation,
  COUNT(*) as operation_count,
  MIN(timestamp) as first_op,
  MAX(timestamp) as last_op,
  MAX(timestamp) - MIN(timestamp) as duration
FROM audit_log
GROUP BY table_name, operation;
```

## Commands & Integration

### Justfile Integration

```bash
# Backup database
just backup-db

# Restore from backup
just restore-db backup_file=db.duckdb.backup.20251221

# Export for analysis
just export-db format=csv

# Check integrity
just db-integrity-check

# Run time-travel query
just db-time-travel transaction_id=T₁
```

### CLI Usage

```bash
# Open DuckDB shell
duckdb /Users/bob/ies/music-topos/db.duckdb

# Run query from command line
duckdb /Users/bob/ies/music-topos/db.duckdb \
  "SELECT COUNT(*) FROM interactions"

# Load SQL file
duckdb /Users/bob/ies/music-topos/db.duckdb < schema.sql
```

## Use Cases in Music-Topos

### Phase 1: Data Acquisition
- Store raw interactions from Bluesky, GitHub, Zulip
- Track provenance with audit logs
- Enable time-travel to any point in history

### Phase 2: Colorable Music Topos
- Store entropy measurements per interaction
- Record leitmotif assignments with confidence scores
- Track color mappings to HSV space

### Phase 3: 5D Pattern Extraction
- Persist feature vectors (39-49 dimensions)
- Store temporal, topic, interaction, learning, network patterns
- Enable multi-layer queries (history → features → unified view)

### Phase 4: Agent-o-rama Training
- **Trace Storage**: Each training epoch → database record
- **Time-Travel Checkpoints**: Restore to best epoch
- **Audit Log**: Record all LLM calls, skill loads, color assignments
- **Causality**: Vector clocks track dependencies between decisions
- **Provenance**: Full lineage from raw data to trained surrogate

## Best Practices Summary

1. **Performance**: Set memory_limit=8GB, use SNAPPY compression, index frequently-queried columns
2. **Temporal**: Track vector clocks, use frozen snapshots, maintain immutable audit logs
3. **Integration**: Use multi-layer queries (history → world → unified), apply refinement pattern
4. **Reliability**: Regular backups, integrity checks, automated archival
5. **Analysis**: Export CSV/JSON/Parquet, maintain statistics views, track mutations

## Example: Complete Workflow

```python
import duckdb
from datetime import datetime

# Initialize
db = duckdb.connect('music_topos.duckdb')

# Create schema with audit triggers
db.execute("""
  CREATE TABLE IF NOT EXISTS interactions (
    id INTEGER PRIMARY KEY,
    user_id VARCHAR,
    content VARCHAR,
    created_at TIMESTAMP,
    vector_clock VARCHAR,
    transaction_id INTEGER
  ) WITH (compression='snappy')
""")

# Insert interaction
db.execute(
  "INSERT INTO interactions (user_id, content, created_at, vector_clock) "
  "VALUES (?, ?, ?, ?)",
  ['alice', 'Technical innovation in algorithms', datetime.now(), '[1, 0, 0]']
)

# Query time-travel
historical = db.execute(
  "SELECT * FROM interactions VERSION AT SYSTEM_TIME AS OF ?",
  [1]
).fetchdf()

# Export for analysis
db.execute(
  "COPY interactions TO 'interactions.csv' WITH (FORMAT CSV, HEADER TRUE)"
)

db.close()
```

---

**Skill Name**: duckdb-temporal-versioning
**Type**: Temporal Database with Time-Travel Queries
**Trit**: +1 (PLUS - generative)
**GF(3)**: Balanced with clj-kondo-3color (-1) + acsets (0)
**SPI**: Guaranteed (same schema + data → same results)
**Applications**: Data acquisition, feature storage, training trace logging, audit trails
