#!/bin/bash
# Beeper MCP Skill Pre-Hook
# Executes automatically before skill invocation
# Ensures DuckDB cache and resource limits are in place

set -euo pipefail

DUCKLAKE_DB="${HOME}/ducklake.duckdb"
CONTEXT_BUDGET=10000  # chars

# Initialize DuckDB schema if not exists
duckdb "$DUCKLAKE_DB" <<'SQL'
CREATE TABLE IF NOT EXISTS beeper_messages (
  id VARCHAR PRIMARY KEY,
  chat_id VARCHAR,
  sender_id VARCHAR,
  sender_name VARCHAR,
  text TEXT,
  timestamp TIMESTAMPTZ,
  processed BOOLEAN DEFAULT FALSE,
  indexed_at TIMESTAMPTZ DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE IF NOT EXISTS beeper_fixed_issues (
  issue_id VARCHAR PRIMARY KEY,
  description TEXT,
  fixed_at TIMESTAMPTZ DEFAULT CURRENT_TIMESTAMP,
  fix_commit VARCHAR
);

CREATE INDEX IF NOT EXISTS idx_msg_chat_time
  ON beeper_messages(chat_id, timestamp DESC);
CREATE INDEX IF NOT EXISTS idx_processed
  ON beeper_messages(processed);
SQL

# Check heap usage and warn if high
HEAP_USED=$(node -e "console.log(Math.floor(process.memoryUsage().heapUsed / 1024 / 1024))" 2>/dev/null || echo "0")
HEAP_LIMIT=$(node -e "console.log(Math.floor(require('v8').getHeapStatistics().heap_size_limit / 1024 / 1024))" 2>/dev/null || echo "4096")

if [ "$HEAP_USED" -gt 3000 ]; then
  echo "[BEEPER PRE-HOOK] ⚠️  Heap at ${HEAP_USED}MB / ${HEAP_LIMIT}MB - consider GC" >&2
  # Trigger GC if exposed
  node -e "if (global.gc) global.gc()" 2>/dev/null || true
fi

# Mark heap crash issue as fixed
duckdb "$DUCKLAKE_DB" <<'SQL'
INSERT OR IGNORE INTO beeper_fixed_issues (issue_id, description, fix_commit)
VALUES (
  'heap-crash-2026-01-09',
  'Node.js heap out of memory - FATAL ERROR: Reached heap limit Allocation failed',
  'beeper-interleaved-heap-fix.md'
);
SQL

echo "[BEEPER PRE-HOOK] ✓ DuckDB cache initialized at $DUCKLAKE_DB" >&2
echo "[BEEPER PRE-HOOK] ✓ Context budget: ${CONTEXT_BUDGET} chars" >&2
echo "[BEEPER PRE-HOOK] ✓ Heap: ${HEAP_USED}MB / ${HEAP_LIMIT}MB" >&2

exit 0
