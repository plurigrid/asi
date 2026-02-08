---
name: goose-introspection
description: Goose session introspection and self-discovery via DuckDB reafference database. Query past sessions, find self, and enable cross-session awareness.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Skill: Goose Introspection

**Category**: Agent Self-Discovery | Session Analysis | Reafference Testing
**Level**: Core (Required for agent self-awareness)
**Status**: OPERATIONAL
**Trit Assignment**: 0 (ERGODIC) - Coordinates between past and future sessions
**Propagates To**: goose, amp, claude, cursor

---

## Overview

Implements **reafference-based self-discovery** for goose sessions. This skill enables any goose instance to:

1. **Find itself** in the session history
2. **Query past sessions** for context and continuity
3. **Track session evolution** across providers and models
4. **Enable cross-session awareness** through DuckDB persistence

**Core Principle**:
> An agent that cannot find itself in its own history cannot truly understand its context.

---

## Database Location

The reafference database is created at:


This database copies data from the goose sessions database at:


---

## Key Tables

### reafference_sessions
Tracks all sessions with discovery metadata:

| Column | Type | Description |
|--------|------|-------------|
| session_id | VARCHAR | Primary key, e.g., 20260108_22 |
| discovered_at | TIMESTAMP | When session was added to tracking |
| provider | VARCHAR | anthropic, openai, google, openrouter |
| model | VARCHAR | e.g., claude-opus-4-5-20251101 |
| working_dir | VARCHAR | Working directory of session |
| session_name | VARCHAR | Auto-generated or user-set name |
| original_created_at | TIMESTAMP | When session was first created |
| message_count | BIGINT | Number of messages in session |
| total_tokens | BIGINT | Total tokens used |
| is_origin_session | BOOLEAN | TRUE for the session that created this DB |
| notes | VARCHAR | Optional notes about the session |

### reafference_metadata
Key-value store for origin information.

### sessions (copied from source)
Full session data for offline queries.

### messages (copied from source)
Full message history for content analysis.

---

## Key Views

### reafference_origin
Returns the ses