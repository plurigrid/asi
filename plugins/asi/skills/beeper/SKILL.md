---
name: beeper
description: Unified messaging via three access tiers — MCP (live API), beeper-cli (authenticated CLI), and direct SQLite→DuckDB (full archive). Search, analyze, and act across all networks. Subsumes beeper-mcp, messaging-world, and signal-messaging.
version: 3.0.0
trit: 0
role: ERGODIC
color: "#6B5CE7"
hue: 249
tags: [messaging, beeper, mcp, beeper-cli, sqlite, duckdb, communication, signal, acset, social-graph]
deployed: 2026-04-04
evolves: beeper-mcp
subsumes: [beeper-mcp, messaging-world, signal-messaging]
---

## CRITICAL: TOKENS PAY RENT

**Every output token must produce actionable value.**

1. **NO PASSIVE SUMMARIES** — extract ACTION ITEMS, DECISIONS, BLOCKERS → create artifacts
2. **NO AGREEMENT WITHOUT IMPLEMENTATION** — "I agree" must be followed by code/file/commit
3. **NO RHETORICAL QUESTIONS** — ask only when you cannot proceed without the answer
4. **Enforcement:** If output contains summary without artifact, STOP and create the artifact first.

---

# Beeper Unified Messaging

Access all messaging networks through three access tiers with increasing depth.

## Three Access Tiers

```
Tier 1: Desktop API (MCP + HTTP)  — real-time chat; send text + attachments
Tier 2: beeper-cli (Auth)         — paginated history, chat type metadata, contacts
Tier 3: SQLite→DuckDB (Archive)   — full offline archive, cross-platform analytics
```

### Tier Selection Decision Tree

```
Need to SEND something?
  └─ Text only → Tier 1 (MCP send_message)
  └─ File/attachment → Tier 1 (Desktop API HTTP: upload + send)

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

---

## Tier 1: Desktop API (MCP + HTTP)

### MCP Tools

| Tool | Purpose |
|------|---------|
| `search_chats` | Search chats by title/network or participants |
| `get_chat` | Get chat metadata (participants, last activity) |
| `list_messages` | List messages in a chat (paged) |
| `search_messages` | Search messages (literal word match, limit ≤ 20) |
| `send_message` | Send a text message |
| `focus_app` | Open Beeper Desktop, prefill draft text/attachment |
| `archive_chat` | Archive/unarchive a chat |
| `set_chat_reminder` | Set reminder for a chat |

```bash
mcp__beeper__search_chats query="contact name"
mcp__beeper__list_messages chatID="..."
mcp__beeper__send_message chatID="..." text="Hello!"
mcp__beeper__focus_app chatID="..." draftText="..." draftAttachmentPath="/path/to/file"
```

**Search is LITERAL WORD MATCHING**, not semantic. Use single keywords.

### Send Attachments (Programmatic)

MCP `send_message` is text-only. For files:
1. `POST /v1/assets/upload` (multipart) → returns `uploadID`
2. `POST /v1/chats/{chatID}/messages` with `attachment.uploadID`

```bash
skills/beeper/scripts/beeper_send_file.sh '<chat_id>' /path/to/file 'optional text'
```

### User Identity

Beeper/Matrix has TWO identifiers per user:
- **Matrix userID**: `@username:beeper.com` (permanent)
- **Display name**: User-chosen (can differ)

Cross-reference `list_messages` to map `senderID` ↔ `senderName`.

---

## Tier 2: beeper-cli (Authenticated CLI)

```bash
# Auth pattern — secret never exposed to context
BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) \
  beeper-cli <command> -o json

# List chats (has type: "single" vs "group")
beeper-cli chats list -o json

# List messages from a chat
beeper-cli messages list -o json --chat-id "..."

# List connected accounts
beeper-cli accounts list -o json

# Filter by account (e.g. WhatsApp)
beeper-cli chats list -o json --account-ids whatsapp
```

### Connected Accounts

| Account | Network | Identity |
|---------|---------|----------|
| hungryserv | Matrix | @zigger:beeper.com |
| local-telegram | Telegram | @physetermacrocephalus |
| whatsapp | WhatsApp | +14153141554 |
| (system) | iMessage | via macOS bridge |

### Caveats
- **Pagination bug**: cursor can cycle — always deduplicate on chat ID
- **iMessage coverage**: ~22 recent chats; chat.db has 354 DMs
- **WhatsApp**: must use `--account-ids whatsapp`

---

## Tier 3: SQLite→DuckDB (Full Archive)

### Database Locations

| Database | Path | Contents |
|----------|------|----------|
| Beeper account.db | `~/Library/Application Support/BeeperTexts/account.db` | Signal + Telegram via Matrix |
| Beeper index.db | `~/Library/Application Support/BeeperTexts/index.db` | Full-text search index |
| iMessage chat.db | `~/Library/Messages/chat.db` | All iMessage/SMS history |

### DuckDB Inline Attach

```sql
INSTALL sqlite; LOAD sqlite;
ATTACH '~/Library/Application Support/BeeperTexts/account.db'
  AS beeper (TYPE sqlite, READ_ONLY);
ATTACH '~/Library/Messages/chat.db'
  AS imessage (TYPE sqlite, READ_ONLY);
```

### Unified DM Landscape Query

```sql
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
            'displayname\\x22:\\x22([^\\]+)', 1) AS display_name
    FROM beeper.local_events le
    WHERE le.type = 'm.room.member'
      AND le.sender <> '@zigger:beeper.com'
      AND le.state_key <> '@zigger:beeper.com'
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
SELECT * FROM beeper_final UNION ALL SELECT * FROM imessage_dms
ORDER BY my_msg_count DESC;
```

### Persisted Table

Results materialized in `~/i.duckdb` as `dm_landscape`:
- Signal: 232 threads (8,569 msgs)
- iMessage: 119 threads (9,192 msgs)
- Telegram: 9 threads (156 msgs)
- Total: 360 threads, 17,917 messages

### Schema Reference

**beeper.local_events**: `room_id, event_id, sender, type, state_key, content BLOB, event_ts INT`
- Content BLOB uses `\x22` instead of `"` — use `regexp_extract` not `json_extract_string`

**imessage.chat**: `ROWID, chat_identifier, display_name, style (43=group)`
**imessage.message**: `ROWID, text, is_from_me, date, handle_id`
Join via `imessage.chat_message_join(chat_id, message_id)`.

---

## ACSet Social Graph Schema

```julia
@present SchMessagingWorld(FreeSchema) begin
  Identity::Ob; Channel::Ob; Account::Ob; Contact::Ob; Conversation::Ob; Network::Ob
  identity_account::Hom(Account, Identity)
  account_channel::Hom(Account, Channel)
  contact_account::Hom(Contact, Account)
  conv_account::Hom(Conversation, Account)
  contact_network::Hom(Contact, Network)
  conv_network::Hom(Conversation, Network)
  Email::AttrType; Name::AttrType; Trit::AttrType; Count::AttrType
  contact_email::Attr(Contact, Email)
  contact_name::Attr(Contact, Name)
  channel_trit::Attr(Channel, Trit)
  contact_count::Attr(Contact, Count)
end
```

### Channel Trit Assignment

```
OUTLOOK (−1)  →  y.shkel@utoronto.ca    (academic, validator)
GMAIL   ( 0)  →  greenteatree01@gmail   (personal, coordinator)
BEEPER  (+1)  →  @greenteatree01:beeper (multi-protocol, generator)
Σ = 0 ✓
```

### Network Topology (50 Active Chats)

- **Signal (18)**: ies, Meta-Org, Cognition Cosmos, Gay.jl, sloppies, Avalon, NYCies + DMs
- **Telegram (15)**: Frontier Tower community channels
- **WhatsApp (6)**: Stanford BJJ, family, salon
- **Discord (5)**: string-parsing-mines, 7-calendar-years + DMs
- **Matrix (3)**: Beeper Dev Community, Vivarium Public

---

## Conversation Branch Tracking

```sql
CREATE TABLE IF NOT EXISTS beeper_conversation_branches (
  branch_id VARCHAR PRIMARY KEY,
  chat_id VARCHAR NOT NULL,
  parent_branch_id VARCHAR,
  topic VARCHAR NOT NULL,
  first_message_id VARCHAR,
  last_message_id VARCHAR,
  status VARCHAR DEFAULT 'open',  -- 'open', 'resolved', 'merged', 'stale'
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  resolved_at TIMESTAMP
);

CREATE TABLE IF NOT EXISTS beeper_branch_transitions (
  from_branch VARCHAR,
  to_branch VARCHAR,
  transition_type VARCHAR,  -- 'fork', 'merge', 'abandon', 'resolve'
  message_id VARCHAR,
  timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (from_branch, to_branch, message_id)
);
```

Branch rules: Fork (one message → multiple topics), Merge (response addresses multiple), Resolve (explicit closure), Abandon (7 days inactive → stale).

---

## Signal via Rust MCP (Direct Channel)

For Signal-only access without Beeper bridge:

```json
{
  "signal": {
    "command": "cargo",
    "args": ["run", "--release", "--example", "signal-server-stdio"],
    "cwd": "/Users/alice/signal-mcp",
    "env": { "RUST_LOG": "signal_mcp=info" }
  }
}
```

Capabilities: send/receive messages, list conversations, handle attachments.
Use `read_mcp_resource` with `signal://` URIs.

---

## GF(3) Triadic Access Pattern

| Trit | Role | Tier | Action |
|------|------|------|--------|
| MINUS (−1) | Validator | SQLite→DuckDB | Verify data exists locally before fetching |
| ERGODIC (0) | Coordinator | beeper-cli | Metadata, routing, account selection |
| PLUS (+1) | Generator | MCP | Send messages, fetch fresh data |

---

## Resource-Aware Processing

**NEVER pull full message history into context.**

1. Check DuckDB first (Tier 3) — zero network cost
2. Use MCP for recent (Tier 1) — bounded by limit param
3. Use beeper-cli for metadata (Tier 2) — chat types, accounts

Context budget: 10,000 chars. Always set `limit` and `dateAfter` params.

---

## MCP Server Config

```json
{
  "beeper": {
    "command": "/bin/sh",
    "args": ["-c", "BEEPER_ACCESS_TOKEN=$(fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt) exec npx -y @beeper/desktop-mcp"]
  }
}
```

Requires: `fnox`, age key at `~/.age/key.txt`, `npx` in PATH, Beeper Desktop running.

---

## Known Issues

- **beeper-cli pagination cycles**: cursor can loop — deduplicate on chat ID
- **Beeper BLOB encoding**: `\x22` escapes — use `regexp_extract`
- **WhatsApp not in account.db**: use beeper-cli for WhatsApp
- **iMessage SQL**: use `<>` not `!=` (shell escaping)
