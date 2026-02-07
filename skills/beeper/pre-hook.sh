#!/bin/bash
# Beeper Unified Skill Pre-Hook (v2.0)
# Ensures DuckDB cache, dm_landscape table, and resource limits

set -euo pipefail

DUCKLAKE_DB="${HOME}/ducklake.duckdb"
DM_DB="${HOME}/i.duckdb"
BEEPER_DB="${HOME}/Library/Application Support/BeeperTexts/account.db"
IMESSAGE_DB="${HOME}/Library/Messages/chat.db"

# Initialize DuckDB message cache schema
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

# Check if dm_landscape needs refresh (older than 1 day or missing)
NEEDS_REFRESH=0
if [ ! -f "$DM_DB" ]; then
  NEEDS_REFRESH=1
else
  AGE=$(duckdb "$DM_DB" -noheader -csv -c "
    SELECT CASE WHEN COUNT(*) = 0 THEN 999
    ELSE 0 END FROM information_schema.tables
    WHERE table_name = 'dm_landscape';
  " 2>/dev/null || echo "999")
  if [ "$AGE" = "999" ]; then
    NEEDS_REFRESH=1
  fi
fi

# Verify SQLite sources exist before attempting refresh
if [ "$NEEDS_REFRESH" = "1" ] && [ -f "$BEEPER_DB" ] && [ -f "$IMESSAGE_DB" ]; then
  echo "[BEEPER PRE-HOOK] Refreshing dm_landscape..." >&2
  duckdb "$DM_DB" <<SQL
INSTALL sqlite; LOAD sqlite;
ATTACH '${BEEPER_DB}' AS beeper (TYPE sqlite, READ_ONLY);
ATTACH '${IMESSAGE_DB}' AS imessage (TYPE sqlite, READ_ONLY);

CREATE OR REPLACE TABLE dm_landscape AS
WITH
beeper_dms AS (
    SELECT le.room_id,
        COUNT(*) FILTER (WHERE le.sender = '@zigger:beeper.com') AS my_msg_count,
        COUNT(DISTINCT le.sender) AS sender_count,
        CASE WHEN le.room_id LIKE '%.local-signal.%' THEN 'Signal'
             WHEN le.room_id LIKE '%.local-telegram.%' THEN 'Telegram'
             ELSE 'Other' END AS network
    FROM beeper.local_events le WHERE le.type = 'm.room.message'
    GROUP BY le.room_id
    HAVING COUNT(*) FILTER (WHERE le.sender = '@zigger:beeper.com') >= 3
       AND COUNT(DISTINCT le.sender) <= 2
),
beeper_names AS (
    SELECT DISTINCT ON (le.room_id) le.room_id,
        regexp_extract(CAST(le.content AS VARCHAR),
            'displayname\\x22:\\x22([^\\\\]+)', 1) AS display_name
    FROM beeper.local_events le
    WHERE le.type = 'm.room.member'
      AND le.sender <> '@zigger:beeper.com' AND le.state_key <> '@zigger:beeper.com'
      AND CAST(le.content AS VARCHAR) NOT LIKE '%bridge bot%'
    ORDER BY le.room_id, le.event_ts DESC
),
beeper_final AS (
    SELECT bd.room_id AS id,
        COALESCE(NULLIF(bn.display_name, ''), 'unnamed') AS contact_name,
        bd.my_msg_count, bd.network, 'beeper_db' AS source
    FROM beeper_dms bd LEFT JOIN beeper_names bn ON bd.room_id = bn.room_id
),
imessage_dms AS (
    SELECT c.chat_identifier AS id,
        COALESCE(NULLIF(c.display_name, ''), c.chat_identifier) AS contact_name,
        COUNT(*) AS my_msg_count, 'iMessage' AS network, 'imessage_db' AS source
    FROM imessage.chat c
    JOIN imessage.chat_message_join cmj ON c.ROWID = cmj.chat_id
    JOIN imessage.message m ON cmj.message_id = m.ROWID
    WHERE m.is_from_me = 1 AND c.style <> 43
    GROUP BY c.ROWID, c.chat_identifier, c.display_name HAVING COUNT(*) >= 3
)
SELECT * FROM beeper_final UNION ALL SELECT * FROM imessage_dms;
SQL
  echo "[BEEPER PRE-HOOK] dm_landscape refreshed" >&2
fi

# Check beeper-cli availability
if [ -x "${HOME}/go/bin/beeper-cli" ]; then
  echo "[BEEPER PRE-HOOK] beeper-cli: available" >&2
else
  echo "[BEEPER PRE-HOOK] beeper-cli: not found at ~/go/bin/beeper-cli" >&2
fi

# Report status
if [ -f "$DM_DB" ]; then
  THREAD_COUNT=$(duckdb "$DM_DB" -noheader -csv -c "
    SELECT COUNT(*) FROM dm_landscape;
  " 2>/dev/null || echo "?")
  echo "[BEEPER PRE-HOOK] dm_landscape: ${THREAD_COUNT} threads in ~/i.duckdb" >&2
fi

echo "[BEEPER PRE-HOOK] DuckDB cache: $DUCKLAKE_DB" >&2
echo "[BEEPER PRE-HOOK] Tiers: MCP (live) + beeper-cli (auth) + SQLite->DuckDB (archive)" >&2

exit 0
