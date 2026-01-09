---
name: beeper-mcp
description: Unified messaging via Beeper Desktop MCP. Search chats, send messages, manage conversations across all networks (iMessage, WhatsApp, Signal, Telegram, Discord, Slack, etc.)
version: 1.1.0
trit: 0
role: ERGODIC
color: "#6B5CE7"
hue: 249
tags: [messaging, beeper, mcp, communication, chat]
deployed: 2026-01-06
pre_hook: pre-hook.sh
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

# Beeper MCP Skill

Access all messaging networks through Beeper's unified interface.

## Quick Start

```
# Search for a chat
mcp__beeper__search "contact name"

# Send a message
mcp__beeper__send_message chatID="..." text="Hello!"

# List recent chats
mcp__beeper__search_chats limit=10
```

## Core Tools

| Tool | Purpose |
|------|---------|
| `search` | Find chats, groups, or people by name |
| `search_chats` | List/filter chats by type, inbox, activity |
| `search_messages` | Find messages by content (literal match) |
| `get_chat` | Get chat details and participants |
| `list_messages` | Get messages from a specific chat |
| `send_message` | Send text message to a chat |
| `archive_chat` | Archive/unarchive a chat |
| `set_chat_reminder` | Set reminder for a chat |
| `focus_app` | Open Beeper Desktop to specific chat |

## Search Guidelines

**CRITICAL**: Queries are LITERAL WORD MATCHING, not semantic search.

- RIGHT: `query="dinner"` or `query="flight"`
- WRONG: `query="dinner plans tonight"` or `query="travel arrangements"`

Multiple words = ALL must match. Use single keywords.

## User Identity Clarification

**IMPORTANT**: Beeper/Matrix has TWO identifiers per user:

1. **Matrix userID**: `@username:beeper.com` (permanent, searchable)
2. **Display name**: User-chosen name (can differ from userID)

Example: User `@jsmith:beeper.com` may have display name "John Smith"

When search finds a match:
- The search matched the **userID** OR **display name**
- Chat participant lists show **display names**, not userIDs
- To see userIDs, use `list_messages` and check `senderID` field

When reporting search results:
- Cross-reference `list_messages` to map `senderID` ↔ `senderName`
- Report as "username (displays as 'Display Name')" for clarity

## Resource-Aware Message Processing

**CRITICAL**: Always work backwards from most recent messages to avoid:
- Re-processing already-handled tasks
- Repeating fixed issues
- Heap exhaustion from loading too much history

### Default Workflow (Backwards-First)

```javascript
// 1. Start with most recent (no cursor = newest first)
const recent = await list_messages(chatID, { limit: 20 });

// 2. Check if already processed (use DuckDB tracking)
const unprocessed = recent.items.filter(msg => !isProcessed(msg.id));

// 3. Process only new messages
for (const msg of unprocessed) {
  await processMessage(msg);
  markProcessed(msg.id);
}

// 4. If need more history, paginate backwards
if (needsMoreContext) {
  const older = await list_messages(chatID, {
    cursor: recent.cursor,
    direction: 'before',
    limit: 20
  });
}
```

### DuckDB Tracking Schema

```sql
CREATE TABLE IF NOT EXISTS beeper_processed_messages (
  message_id VARCHAR PRIMARY KEY,
  chat_id VARCHAR,
  processed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  task_extracted BOOLEAN,
  issue_status VARCHAR  -- 'open', 'fixed', 'duplicate'
);

CREATE INDEX idx_msg_chat ON beeper_processed_messages(chat_id, processed_at DESC);
```

### Check Before Processing

```javascript
function isAlreadyFixed(messageText) {
  // Query DuckDB for similar fixed issues
  const similar = db.query(`
    SELECT issue_id, description
    FROM fixed_issues
    WHERE description % ?  -- Full-text similarity
    LIMIT 1
  `, [messageText]);

  if (similar.length > 0) {
    console.warn(`⚠️ Similar issue already fixed: ${similar[0].description}`);
    return true;
  }
  return false;
}
```

## Workflow Patterns

### Find and Message Someone
1. `search "person name"` - Get chatID
2. **Verify identity**: `list_messages chatID="..." limit=5` - Check recent messages ONLY
3. `send_message chatID="..." text="..."`

### Identify Users in a Chat
1. `list_messages chatID="..." limit=10` - Get RECENT messages only (not entire history)
2. Map userID ↔ displayName from the subset

### Search Message History (Resource-Aware)
1. `search_chats` to get chatIDs of relevant chats
2. `search_messages chatIDs=[...] query="keyword" limit=20 dateAfter="2026-01-08T00:00:00Z"`
3. **Never omit dateAfter** - prevents loading entire chat history

### Monitor Unread
```
search_chats unreadOnly=true inbox="primary" limit=10
```

### Filter by Network
Use `accountIDs` parameter after getting accounts via `get_accounts`.

## Message Formatting

Messages support Markdown. Use sparingly for clarity.

## Chat Types

- `single` - Direct messages (1:1)
- `group` - Group chats
- `any` - All types

## Inbox Filters

- `primary` - Non-archived, non-low-priority
- `low-priority` - Low priority inbox
- `archive` - Archived chats

## Resource-Aware Random Walk Pattern

**NEVER pull full message history into context.** Instead:

### 1. Query in DuckDB First
```sql
-- Store messages incrementally, query locally
CREATE TABLE IF NOT EXISTS beeper_messages (
  id VARCHAR PRIMARY KEY,
  chat_id VARCHAR,
  sender_id VARCHAR,
  sender_name VARCHAR,
  text TEXT,
  timestamp TIMESTAMPTZ,
  processed BOOLEAN DEFAULT FALSE
);

-- Sample recent messages via random walk
SELECT * FROM beeper_messages
WHERE chat_id = ?
ORDER BY RANDOM()  -- Ergodic sampling
LIMIT 5;
```

### 2. TreeSitter for Structure Extraction
```bash
# Extract code blocks from messages without loading full text
tree-sitter parse --scope source.markdown message.md \
  | grep -E "(fenced_code_block|code_span)"
```

### 3. Triadic Walker Pattern
```
MINUS (-1): Validate message exists in DuckDB before fetching
ERGODIC (0): Random walk sample from local cache
PLUS (+1): Fetch ONLY if not in cache, with strict limit
```

### 4. Context Budget Enforcement
```python
CONTEXT_BUDGET = 10000  # chars
current_context = 0

def safe_fetch(chat_id, limit=5):
    # Check DuckDB cache first
    cached = db.query("SELECT * FROM beeper_messages WHERE chat_id = ? LIMIT ?", chat_id, limit)
    if len(cached) >= limit:
        return cached  # Zero network cost

    # Fetch only missing, with limit
    remaining = limit - len(cached)
    fresh = mcp__beeper__list_messages(chatID=chat_id, limit=remaining)

    # Enforce budget
    for msg in fresh.items:
        msg_size = len(msg.get('text', ''))
        if current_context + msg_size > CONTEXT_BUDGET:
            break
        current_context += msg_size
        db.insert("beeper_messages", msg)

    return db.query("SELECT * FROM beeper_messages WHERE chat_id = ? LIMIT ?", chat_id, limit)
```

### 5. SICP Lazy Evaluation
```scheme
;; Don't fetch until actually needed
(define (beeper-messages chat-id)
  (delay
    (mcp__beeper__list_messages chatID: chat-id limit: 5)))

;; Only force when required
(define (get-latest-sender chat-id)
  (let ((msgs (force (beeper-messages chat-id))))
    (cdar msgs)))  ; Just sender from first message
```

## GF(3) Integration

This skill operates as ERGODIC (0) in triadic compositions:
- Coordinates message flow between networks
- Synthesizes cross-platform conversations
- Neutral hub for communication triads

### Triadic Fetch Strategy
| Trit | Role | Beeper Action |
|------|------|---------------|
| MINUS (-1) | Validator | Check DuckDB cache, reject if stale |
| ERGODIC (0) | Coordinator | Random walk sample, enforce budget |
| PLUS (+1) | Generator | Fetch fresh data, strict `limit` param |

## MCP Server Config

```json
{
  "beeper": {
    "command": "/bin/sh",
    "args": [
      "-c",
      "BEEPER_ACCESS_TOKEN=$(/Users/alice/.cargo/bin/fnox get BEEPER_ACCESS_TOKEN --age-key-file /Users/alice/.age/key.txt) exec npx -y @beeper/desktop-mcp"
    ]
  }
}
```

Requires:
- `fnox` at `/Users/alice/.cargo/bin/fnox`
- Age key at `/Users/alice/.age/key.txt`
- `npx` in PATH
- Beeper Desktop running
