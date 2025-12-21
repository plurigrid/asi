# discohy-streams - Discopy Color Streams via Hy

## Overview

Provides personalized color streams using discopy categorical diagrams via Hy (discohy). Each human gets a self-learning color embedding with 3 parallel streams.

## Core Concepts

### 3 Parallel Streams (Balanced Ternary)

```
color://human-id/LIVE      → +1 (forward, real-time)
color://human-id/VERIFY    →  0 (verification, BEAVER)
color://human-id/BACKFILL  → -1 (historical, archived)
```

### Discopy Integration

```hy
;; Create color chain diagram
(import [discopy.monoidal [Ty Box]])
(setv Color (Ty "Color"))
(setv boxes [(Box "C1" Color Color)
             (Box "C2" Color Color)
             (Box "C3" Color Color)])
(setv diagram (>> (get boxes 0) (get boxes 1) (get boxes 2)))
```

### GayMCP color:// Resource

```
color://alice           → All 3 streams simultaneously
color://alice/LIVE      → Current LIVE color
color://alice/VERIFY/5  → Time travel to index 5
```

## Usage

```hy
#!/usr/bin/env hy
(import [gay_world_ducklake [create-gay-world color-at]])

;; Create world
(setv world (create-gay-world 0x42D))

;; Get surface for human
(setv surface (.get-or-create-surface (get world "world") "bob"))

;; Get simultaneous colors
(setv colors (.get-simultaneous-colors surface))

;; Access via MCP
(setv mcp (get world "mcp"))
(.get-resource mcp "color://bob/LIVE")
```

## Self-Learning Embedding

Each stream maintains a learnable embedding for color preferences:

```hy
(setv stream surface.live-stream)

;; Generate color
(setv color (.next-color stream))

;; Learn from preference
(.learn stream color True)   ; liked
(.learn stream color False)  ; disliked

;; Get prediction
(.predict stream color)  ; → 0.0-1.0
```

## Time Travel

```hy
;; Travel to specific index
(.time-travel surface 10 "LIVE")

;; Mark pattern as disallowed
(.mark-disallowed surface 10 5 TAP-LIVE)

;; Attempt disallowed travel → error
(.time-travel surface 5 "LIVE")
```

## DuckDB Integration

```sql
-- Query color history
SELECT * FROM color_history
WHERE stream_id LIKE 'alice%'
ORDER BY timestamp DESC;

-- View time travel log
SELECT * FROM time_travel_log
WHERE status = 'DISALLOWED';
```

## Configuration

```toml
[discohy-streams]
seed = 1069  # 0x42D
streams = ["LIVE", "VERIFY", "BACKFILL"]
learning_rate = 0.1
db_path = ":memory:"
```

## See Also

- `plurigrid/discohy` - Hy wrapper for discopy
- `gay_world_ducklake.hy` - Full implementation
- `unified_verification_bridge.jl` - 1/4 verification
