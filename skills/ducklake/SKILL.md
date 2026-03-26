---
name: ducklake
description: Create, query, migrate, and maintain DuckLake lakehouse databases using the DuckDB ducklake extension. Use when working with DuckLake catalogs, time travel queries, snapshots, schema evolution, cross-lake federation, or migrating plain DuckDB files to DuckLake format.
---

# DuckLake

DuckLake is an integrated data lake and catalog format from the DuckDB team. It stores metadata in a catalog database (DuckDB, PostgreSQL, SQLite, MySQL) and data as Parquet files. MIT licensed.

Docs: https://ducklake.select/docs/stable/

## Setup

```sql
INSTALL ducklake;
LOAD ducklake;
```

## Connecting

```sql
-- DuckDB catalog (auto-creates if not exists, data in .files/ sibling dir)
ATTACH 'ducklake:my_catalog.ducklake' AS my_lake;

-- PostgreSQL catalog + S3 storage
ATTACH 'ducklake:postgres:dbname=catalog host=pg_host' AS my_lake (DATA_PATH 's3://bucket/data/');

-- SQLite catalog
ATTACH 'ducklake:sqlite:metadata.sqlite' AS my_lake (DATA_PATH 'data_files/');

-- Read-only
ATTACH 'ducklake:my_catalog.ducklake' (READ_ONLY);

-- At specific snapshot
ATTACH 'ducklake:my_catalog.ducklake' (SNAPSHOT_VERSION 3);
ATTACH 'ducklake:my_catalog.ducklake' (SNAPSHOT_TIME '2025-01-15 00:00:00');
```

## Snapshots

Every mutation creates a snapshot. List them:

```sql
SELECT * FROM my_lake.snapshots();
SELECT * FROM my_lake.current_snapshot();
```

Add commit messages inside transactions:

```sql
BEGIN;
INSERT INTO my_lake.events VALUES (...);
CALL my_lake.set_commit_message('alice', 'Daily ingest', extra_info => '{"source": "amp"}');
COMMIT;
```

## Time Travel

```sql
SELECT * FROM tbl AT (VERSION => 3);
SELECT * FROM tbl AT (TIMESTAMP => now() - INTERVAL '1 week');
```

## Schema Evolution

Add/drop/rename columns freely. Each change creates a new snapshot:

```sql
ALTER TABLE my_lake.tbl ADD COLUMN new_col VARCHAR;
ALTER TABLE my_lake.tbl DROP COLUMN old_col;
ALTER TABLE my_lake.tbl RENAME COLUMN x TO y;
```

## Cross-Lake Federation

Attach multiple DuckLakes and JOIN across them:

```sql
ATTACH 'ducklake:lake_a.ducklake' AS a;
ATTACH 'ducklake:lake_b.ducklake' AS b;
SELECT * FROM a.events JOIN b.users ON a.events.user_id = b.users.id;
```

## Maintenance

Run periodically or use `CHECKPOINT`:

```sql
-- Merge small Parquet files (after many small inserts)
CALL my_lake.merge_adjacent_files('my_table');

-- Expire old snapshots (frees time travel before cutoff)
CALL my_lake.expire_snapshots(TIMESTAMP '2025-01-01');

-- Cleanup unreferenced files after expiry
CALL my_lake.cleanup_files();

-- Rewrite files with many deletes
CALL my_lake.rewrite_data_files('my_table');

-- All-in-one
CHECKPOINT my_lake;
```

## Migrating DuckDB to DuckLake

`COPY FROM DATABASE` works but fails on:
- **Non-literal defaults** (e.g., `CURRENT_TIMESTAMP`) -- use `CREATE TABLE AS SELECT` instead
- **PRIMARY KEY / UNIQUE constraints** -- not supported in DuckLake by design

Workaround pattern:

```sql
ATTACH 'old.duckdb' AS src;
ATTACH 'ducklake:new.ducklake' AS dst;
CREATE TABLE dst.my_table AS SELECT * FROM src.my_table;
```

## Unsupported Features

**Will not be supported:** PRIMARY KEY, UNIQUE, FOREIGN KEY, indexes, sequences, VARINT, BITSTRING, UNION types.

**May be supported later:** User-defined types, ARRAY type, ENUM type, CHECK constraints, non-literal defaults, generated columns, macros.

**Extension limitations:** Data inlining only works with DuckDB catalogs. MySQL catalogs not fully supported.

## Advanced Features

- **Partitioning**: `ALTER TABLE tbl ADD PARTITION (col)`
- **Data inlining**: Small tables stored inline in catalog (DuckDB catalogs only): `ATTACH ... (DATA_INLINING_ROW_LIMIT 1000)`
- **Encryption**: `ATTACH ... (ENCRYPTED true)`
- **Row lineage**: Track row-level provenance
- **Views**: `CREATE VIEW my_lake.v AS SELECT ...`
- **Data change feed**: Query changes between snapshots
- **Upserting**: Via `MERGE INTO` (not `INSERT ON CONFLICT` since no PKs)
- **Secrets**: Persist connection config: `CREATE PERSISTENT SECRET (TYPE ducklake, METADATA_PATH '...', DATA_PATH '...')`
