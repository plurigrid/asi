---
name: fswatch-duckdb
description: FileSystemWatcher over /tmp with DuckDB/DuckLake persistence. Auto-starts on Amp sessions for resilient file monitoring with temporal queries.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# FileSystemWatcher + DuckDB Skill

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - coordination/observation)
**Principle**: Observe filesystem changes, persist to DuckDB, query temporally
**GF(3) Balanced Triad**:
- fswatch-duckdb (0) [Coordinator: Watch/observe]
- duckdb-temporal-versioning (+1) [Generator: Store events]
- clj-kondo-3color (-1) [Validator: Verify integrity]

---

## Overview

Resilient filesystem monitoring with:
1. **fswatch** or **watchman** for native file events
2. **DuckDB** for persistent event storage with time-travel
3. **DuckLake** patterns for partitioned, versioned storage
4. **Auto-start** on every Amp session

## Auto-Initialization (MANDATORY)

On every Amp session start, run:

```bash
# Initialize watcher database
duckdb ~/.agents/fswatch.duckdb <<'SQL'
CREATE TABLE IF NOT EXISTS fs_events (
  id INTEGER PRIMARY KEY,
  path VARCHAR NOT NULL,
  event_type VARCHAR NOT NULL,  -- 'created', 'modified', 'deleted', 'renamed'
  old_path VARCHAR,             -- for renames
  size BIGINT,
  mtime TIMESTAMP,
  checksum VARCHAR,             -- md5 for dedup
  session_id VARCHAR,           -- Amp thread ID
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  trit INTEGER DEFAULT 0        -- GF(3) color
);

CREATE INDEX IF NOT EXISTS idx_fs_events_path ON fs_events(path);
CREATE INDEX IF NOT EXISTS idx_fs_events_session ON fs_events(session_id);
CREATE INDEX IF NOT EXISTS idx_fs_events_time ON fs_events(created_at);
SQL
```

## Watch /tmp with fswatch

### Start Watcher (Background Daemon)

```bash
# Using fswatch (macOS/Linux)
fswatch -0 -r /tmp | while IFS= read -r -d '' path; do
  event_type="modified"
  if [ ! -e "$path" ]; then
    event_type="deleted"
  elif [ ! -s "$path.prev" 2>/dev/null ]; then
    event_type="created"
  fi
  
  size=$(stat -f%z "$path" 2>/dev/null || echo 0)
  mtime=$(stat -f%m "$path" 2>/dev/null || date +%s)
  checksum=$(md5 -q "$path" 2>/dev/null || echo "")
  
  duckdb ~/.agents/fswatch.duckdb \
    "INSERT IN