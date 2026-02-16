---
name: beeper
description: Unified messaging via three access tiers — MCP (live API), beeper-cli (authenticated CLI), and direct SQLite→DuckDB (full archive). Search, analyze, and act across all networks.
version: 2.0.0
trit: 0
role: ERGODIC
color: "#6B5CE7"
hue: 249
tags: [messaging, beeper, mcp, beeper-cli, sqlite, duckdb, communication]
deployed: 2026-01-31
pre_hook: pre-hook.sh
evolves: beeper-mcp
---

## CRITICAL: TOKENS PAY RENT

**Every output token must produce actionable value.** Violations:

1. **NO PASSIVE SUMMARIES** - Regurgitating conversation content without action items, code, or artifacts is FORBIDDEN
2. **NO AGREEMENT WITHOUT IMPLEMENTATION** - "I agree with X" must be followed by code/file/commit implementing X
3. **NO RHETORICAL QUESTIONS** - Ask only when you cannot proceed without the answer
4. **NO PRAISE/VALIDATION** - Skip "great question" / "you're right" - proceed to work

**When reviewing message history:**
- Extract ACTION ITEMS → create files, send messages, write code
- Extract DECISIONS → update configs, create artifacts documenting the decision
- Extract BLOCKERS → file issues, send follow-up messages
- NEVER just summarize what was discussed

**Enforcement:** If output contains summary without artifact, STOP and create the artifact first.

# Beeper Unified Messaging Skill

Access all messaging networks through three access tiers with increasing depth.

## Three Access Tiers

```
Tier 1: MCP (Live)          — real-time chat, send messages, search
Tier 2: beeper-cli (Auth)   — paginated history, chat type metadata, contacts
Tier 3: SQLite→DuckDB (Archive) — full offline archive, cross-platform analytics
```

### When to Use Which Tier

| Need | Tier | Why |
|------|------|-----|
| Send a message | MCP | Only tier that can write |
| Search recent chats | MCP | Fast, live data |
| List all DMs vs groups | beeper-cli | Has `type: "single"` field |
| WhatsApp/iMessage chats | beeper-cli | Covers networks MCP misses |
| Full message history | SQLite→DuckDB | Complete archive, no pagination limits |
| Cross-platform analytics | SQLite→DuckDB | JOIN across Signal + iMessage + Telegram |
| Contact resolution | SQLite→DuckDB | m.room.member events have display names |

## Tier 1: MCP (Live API)

```
# Search for a chat
mcp__beeper__search_chat_names "contact name"

# Send a message — MCP ONLY, other tiers are read-only
mcp__beeper__send_message chatID="..." text="Hello!"

# List recent chats
mcp__beeper__list_chats limit=10

# Get messages from a chat
mcp__beeper__get_messages chatID="..."

# Search message content
mcp__beeper__search_message_contents query="keyword"
```

### MCP Tools

| Tool | Purpose |
|------|---------|
| `list_chats` | List/filter chats by type, inbox, activity |
| `search_chat_names` | Find chats by name |
| `search_message_contents` | Find messages by content (literal match) |
| `get_messages` | Get messages from a specific chat |
| `get_person_messages` | Get all messages from a specific person |
| `send_message` | Send text message to a chat |

## Tier 2: beeper-cli (Authenticated CLI)

Requires fnox for auth. Binary at `/Users/bob/go/bin/beeper-cli`.

```bash
# Auth pattern — secret never exposed to context
BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) \
  /Users/bob/go/bin/beeper-cli <command> -o json

# List chats (has type: "single" vs "group" — more reliable than MCP)
BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) \
  /Users/bob/go/bin/beeper-cli chats list -o json

# List messages from a chat
BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) \
  /Users/bob/go/bin/beeper-cli messages list -o json --chat-id "..."

# List connected accounts (Signal, Telegram, WhatsApp, iMessage)
BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) \
  /Users/bob/go/bin/beeper-cli accounts list -o json

# Filter by account
BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) \
  /Users/bob/go/bin/beeper-cli chats list -o json --account-ids whatsapp

# Pagination (cursor-based)
BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) \
  /Users/bob/go/bin/beeper-cli chats list -o json --cursor "..." --direction before
```

### beeper-cli Caveats

- **Pagination bug**: cursor can cycle — always deduplicate on chat ID
- **No `--limit` flag**: uses cursor pagination only
- **iMessage coverage**: shows ~22 recent chats; chat.db has 354 DMs
- **WhatsApp**: separate account, must use `--account-ids whatsapp`

### Connected Accounts

| Account | Network | Identity |
|---------|---------|----------|
| hungryserv | Matrix | @zigger:beeper.com (fullName: barton) |
| local-telegram | Telegram | @physetermacrocephalus |
| whatsapp | WhatsApp | +14153141554 |
| (system) | iMessage | via macOS bridge |

## Tier 3: SQLite→DuckDB (Full Archive)

Direct database access for complete offline analysis. DuckDB attaches SQLite databases inline — no ETL needed.

### Database Locations

| Database | Path | Size | Contents |
|----------|------|------|----------|
| Beeper account.db | `~/Library/Application Support/BeeperTexts/account.db` | ~212MB | Signal + Telegram via Matrix protocol |
| Beeper index.db | `~/Library/Application Support/BeeperTexts/index.db` | ~641MB | Full-text search index |
| iMessage chat.db | `~/Library/Messages/chat.db` | ~43MB | All iMessage/SMS history |

### DuckDB Inline Attach Pattern

```sql
INSTALL sqlite;
LOAD sqlite;

-- Attach both databases read-only
ATTACH '~/Library/Application Support/BeeperTexts/account.db'
  AS beeper (TYPE sqlite, READ_ONLY);
ATTACH '~/Library/Messages/chat.db'
  AS imessage (TYPE sqlite, READ_ONLY);

-- Now query across both with standard SQL
SELECT * FROM beeper.local_events LIMIT 1;
SELECT * FROM imessage.chat LIMIT 1;
```

### Unified DM Landscape Query

The canonical cross-platform DM analysis query:

```sql
INSTALL sqlite;
LOAD sqlite;

ATTACH '~/Library/Application Support/BeeperTexts/account.db'
  AS beeper (TYPE sqlite, READ_ONLY);
ATTACH '~/Library/Messages/chat.db'
  AS imessage (TYPE sqlite, READ_ONLY);

WITH
-- Beeper Signal + Telegram DMs (3+ user messages, ≤2 senders = DM)
beeper_dms AS (
    SELECT
        le.room_id,
        COUNT(*) FILTER (WHERE le.sender = '@zigger:beeper.com') AS my_msg_count,
        COUNT(DISTINCT le.sender) AS sender_count,
        CASE
            WHEN le.room_id LIKE '%.local-signal.%' THEN 'Signal'
            WHEN le.room_id LIKE '%.local-telegram.%' THEN 'Telegram'
            ELSE 'Other'
        END AS network
    FROM beeper.local_events le
    WHERE le.type = 'm.room.message'
    GROUP BY le.room_id
    HAVING COUNT(*) FILTER (WHERE le.sender = '@zigger:beeper.com') >= 3
       AND COUNT(DISTINCT le.sender) <= 2
),

-- Resolve display names via regex on BLOB content
-- (BLOBs use \x22 escapes instead of standard JSON quotes)
beeper_names AS (
    SELECT DISTINCT ON (le.room_id)
        le.room_id,
        regexp_extract(
            CAST(le.content AS VARCHAR),
            'displayname\\x22:\\x22([^\\]+)',
            1
        ) AS display_name
    FROM beeper.local_events le
    WHERE le.type = 'm.room.member'
      AND le.sender <> '@zigger:beeper.com'
      AND le.state_key <> '@zigger:beeper.com'
      AND CAST(le.content AS VARCHAR) NOT LIKE '%bridge bot%'
    ORDER BY le.room_id, le.event_ts DESC
),

beeper_final AS (
    SELECT
        bd.room_id AS id,
        COALESCE(NULLIF(bn.display_name, ''), 'unnamed') AS contact_name,
        bd.my_msg_count, bd.network, 'beeper_db' AS source
    FROM beeper_dms bd
    LEFT JOIN beeper_names bn ON bd.room_id = bn.room_id
),

-- iMessage DMs (style != 43 excludes groups)
imessage_dms AS (
    SELECT
        c.chat_identifier AS id,
        COALESCE(NULLIF(c.display_name, ''), c.chat_identifier) AS contact_name,
        COUNT(*) AS my_msg_count,
        'iMessage' AS network,
        'imessage_db' AS source
    FROM imessage.chat c
    JOIN imessage.chat_message_join cmj ON c.ROWID = cmj.chat_id
    JOIN imessage.message m ON cmj.message_id = m.ROWID
    WHERE m.is_from_me = 1 AND c.style <> 43
    GROUP BY c.ROWID, c.chat_identifier, c.display_name
    HAVING COUNT(*) >= 3
)

SELECT * FROM beeper_final
UNION ALL
SELECT * FROM imessage_dms
ORDER BY my_msg_count DESC;
```

### Persisted DM Landscape Table

Results are materialized in `~/i.duckdb` as `dm_landscape`:

```sql
-- Quick summary
duckdb ~/i.duckdb -c "
SELECT network, COUNT(*) AS threads, SUM(my_msg_count) AS total_my_msgs
FROM dm_landscape GROUP BY ALL ORDER BY threads DESC;
"
-- Signal: 232 threads (8,569 msgs)
-- iMessage: 119 threads (9,192 msgs)
-- Telegram: 9 threads (156 msgs)
-- Total: 360 threads, 17,917 messages
```

### Schema Reference

**beeper.local_events** (Matrix protocol):
```
room_id TEXT, event_id TEXT, sender TEXT, type TEXT,
state_key TEXT, content BLOB, redacts TEXT, unsigned BLOB,
stream_order INT, event_ts INT, created_ts INT
```

Key event types:
- `m.room.message` — chat messages (sender, content with body)
- `m.room.member` — join/leave (content has displayname, membership)
- `m.room.name` — room name changes

Content BLOB quirk: uses `\x22` instead of `"` — use `regexp_extract` not `json_extract_string`.

**imessage.chat**:
```
ROWID, chat_identifier, display_name, style (43=group)
```

**imessage.message**:
```
ROWID, text, is_from_me, date, handle_id
```

Join via `imessage.chat_message_join(chat_id, message_id)`.

## Search Guidelines

**MCP queries are LITERAL WORD MATCHING**, not semantic search.

- RIGHT: `query="dinner"` or `query="flight"`
- WRONG: `query="dinner plans tonight"`

Multiple words = ALL must match. Use single keywords.

For semantic/complex searches, use Tier 3 (DuckDB full-text search on SQLite archive).

## Tier Selection Decision Tree

```
Need to SEND a message?
  └─ Yes → Tier 1 (MCP only)

Need chat type (DM vs group)?
  └─ Yes → Tier 2 (beeper-cli has type: "single"|"group")

Need full history or cross-platform JOIN?
  └─ Yes → Tier 3 (SQLite→DuckDB)

Need real-time / recent?
  └─ Yes → Tier 1 (MCP) or Tier 2 (beeper-cli)

Need contact name resolution?
  └─ MCP has senderName in messages
  └─ beeper-cli has title field on chats
  └─ SQLite has m.room.member displayname (most complete)
```

## Workflow Patterns

### Find and Message Someone
1. `mcp__beeper__search_chat_names "person name"` → get chatID
2. `mcp__beeper__get_messages chatID="..." limit=5` → verify identity
3. `mcp__beeper__send_message chatID="..." text="..."`

### DM Landscape Analysis (Tier 3)
```bash
duckdb ~/i.duckdb -c "
SELECT contact_name, my_msg_count, network
FROM dm_landscape
ORDER BY my_msg_count DESC LIMIT 20;
"
```

### Cross-Platform Contact Lookup (Tier 3)
```sql
-- Find someone across Signal + iMessage + Telegram
INSTALL sqlite; LOAD sqlite;
ATTACH '~/Library/Application Support/BeeperTexts/account.db' AS beeper (TYPE sqlite, READ_ONLY);
ATTACH '~/Library/Messages/chat.db' AS imessage (TYPE sqlite, READ_ONLY);

-- Search Beeper (Signal/Telegram)
SELECT DISTINCT
    regexp_extract(CAST(content AS VARCHAR),
        'displayname\\x22:\\x22([^\\]+)', 1) AS name,
    room_id
FROM beeper.local_events
WHERE type = 'm.room.member'
  AND CAST(content AS VARCHAR) LIKE '%SearchName%';

-- Search iMessage
SELECT chat_identifier, display_name
FROM imessage.chat
WHERE display_name LIKE '%SearchName%'
   OR chat_identifier LIKE '%SearchName%';
```

### Filter by Network (Tier 2)
```bash
# Get account IDs
BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) \
  /Users/bob/go/bin/beeper-cli accounts list -o json

# Filter chats to WhatsApp only
BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) \
  /Users/bob/go/bin/beeper-cli chats list -o json --account-ids whatsapp
```

### Refresh dm_landscape Table
```bash
duckdb ~/i.duckdb -c "
INSTALL sqlite; LOAD sqlite;
ATTACH '\$HOME/Library/Application Support/BeeperTexts/account.db' AS beeper (TYPE sqlite, READ_ONLY);
ATTACH '\$HOME/Library/Messages/chat.db' AS imessage (TYPE sqlite, READ_ONLY);

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
            'displayname\\\\x22:\\\\x22([^\\\\]+)', 1) AS display_name
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

SELECT network, COUNT(*) AS threads, SUM(my_msg_count) AS total_my_msgs
FROM dm_landscape GROUP BY ALL ORDER BY threads DESC;
"
```

## Resource-Aware Processing

**NEVER pull full message history into context.** Tier hierarchy:

1. **Check DuckDB first** (Tier 3) — zero network cost
2. **Use MCP for recent** (Tier 1) — bounded by limit param
3. **Use beeper-cli for metadata** (Tier 2) — chat types, accounts

### Context Budget
```
CONTEXT_BUDGET = 10000 chars
Always set limit param on MCP calls.
Always use dateAfter on search_message_contents.
Prefer DuckDB queries over fetching raw messages.
```

## GF(3) Triadic Access Pattern

| Trit | Role | Tier | Action |
|------|------|------|--------|
| MINUS (-1) | Validator | SQLite→DuckDB | Verify data exists locally before fetching |
| ERGODIC (0) | Coordinator | beeper-cli | Metadata, routing, account selection |
| PLUS (+1) | Generator | MCP | Send messages, fetch fresh data |

Conservation: all three tiers complement without overlap. MCP writes, beeper-cli routes, DuckDB archives.

## Known Issues

- **beeper-cli pagination cycles**: cursor-based pagination can return duplicates; always deduplicate on chat ID
- **Beeper BLOB encoding**: content column uses `\x22` escapes — use `regexp_extract`, not `json_extract_string`
- **iMessage chat.db SQL**: use `<>` not `!=` (shell escaping issue)
- **WhatsApp in account.db**: WhatsApp bridge stores data differently; not present in account.db `local_events` — use beeper-cli for WhatsApp

## MCP Server Config

```json
{
  "beeper": {
    "command": "/bin/sh",
    "args": [
      "-c",
      "BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) exec npx -y @beeper/desktop-mcp"
    ]
  }
}
```

Requires: `fnox`, age key at `~/.age/key.txt`, `npx` in PATH, Beeper Desktop running.
