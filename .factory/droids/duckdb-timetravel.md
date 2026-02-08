---
name: duckdb-timetravel
description: ' Layer 3: Temporal Versioning and ACSet Schema Generation for DuckDB'
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# duckdb-timetravel

> Layer 3: Temporal Versioning and ACSet Schema Generation for DuckDB

**Version**: 1.0.0  
**Trit**: 0 (Ergodic - coordinates data flow)  
**Bundle**: database  

## Overview

DuckDB-timetravel provides temporal versioning for interaction data, enabling queries across historical states. It integrates with ACSets for schema generation and supports DuckLake-style snapshots.

## Capabilities

### 1. temporal-query

Query data at specific points in time.

```sql
-- DuckLake-style time travel
SELECT * FROM interactions 
AT (VERSION => 3);

-- Snapshot at specific timestamp
ATTACH 'ducklake:interactions.db' 
  (SNAPSHOT_TIME '2024-11-30 00:00:00');

-- Query historical state
SELECT * FROM interactions
WHERE created_at < '2024-11-30'
AS OF TIMESTAMP '2024-11-15';
```

### 2. version-management

Create and manage temporal versions.

```python
from duckdb_timetravel import VersionManager

vm = VersionManager("interactions.duckdb")

# Create checkpoint
version_id = vm.checkpoint(
    message="Before pattern training",
    seed=0xf061ebbc2ca74d78
)

# List versions
versions = vm.list_versions()
# [
#   {id: 1, timestamp: "2024-11-01", message: "Initial import"},
#   {id: 2, timestamp: "2024-11-15", message: "Added network data"},
#   {id: 3, timestamp: "2024-11-30", message: "Before pattern training"}
# ]

# Restore to version
vm.restore(version_id=2)
```

### 3. acset-schema-gen

Generate DuckDB schemas from ACSet definitions.

```python
from duckdb_timetravel import ACSsetSchemaGenerator

gen = ACSsetSchemaGenerator()

# From ACSet category definition
schema = gen.from_acset("""
@acset ThreadOperad begin
    Thread::Ob
    Concept::Ob
    touches::Hom(Thread, Concept)
    parent::Hom(Thread, Thread)
    trit::Attr(Thread, Int)
    color_h::Attr(Thread, Float)
end
""")

# Generates:
# CREATE TABLE threads (
#     id VARCHAR PRIMARY KEY,
#     parent_id VARCHAR REFERENCES threads(id),
#     trit INT CHECK (trit IN (-1, 0, 1)),
#     color_h FLOAT CHECK (c