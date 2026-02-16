---
name: ducklake-temporal-introspection
description: Time-travel queries and temporal versioning for DuckLake
---

# Ducklake Temporal Introspection

**Version:** 1.0.0
**Status:** Production Ready
**Created:** 2025-12-21
**Canonical Seed:** 0x6475636b6c616b65

## Overview

Loads temporal analysis from Subagent 1 (Data Collector) and provides introspection functions for analyzing ducklake mentions across Claude conversation history.

## Purpose

Enable temporal navigation and clustering analysis of ducklake mentions with:
- 18 total mentions across 12 sessions
- 7-day span (2025-12-15 to 2025-12-22)
- Peak activity detection
- Session duration analysis
- Project distribution tracking

## Data Sources

- **Primary:** `/Users/bob/ies/ducklake_temporal_analysis.json`
- **Secondary:** `~/.claude/history.jsonl`
- **Schema:** VERS_DUCKLAKE_SCHEMA.sql

## Functions

### query_by_timestamp(range: str) -> dict

Query mentions within a timestamp range.

```python
# Example
result = query_by_timestamp("2025-12-21 19:00:00", "2025-12-21 23:00:00")
# Returns: {"mentions": 5, "sessions": 3, "lines": [1035, 1036, 1067, 1073, 1093]}
```

**Implementation:**
```python
import json
from datetime import datetime

def query_by_timestamp(start: str, end: str) -> dict:
    with open("/Users/bob/ies/ducklake_temporal_analysis.json") as f:
        data = json.load(f)

    start_dt = datetime.fromisoformat(start)
    end_dt = datetime.fromisoformat(end)

    mentions = []
    for sample in data["detailed_samples"]:
        ts = datetime.fromisoformat(sample["timestamp"])
        if start_dt <= ts <= end_dt:
            mentions.append(sample)

    return {
        "mentions": len(mentions),
        "sessions": len(set(m["sessionId"] for m in mentions)),
        "lines": [m["line_number"] for m in mentions],
        "contexts": [m["display_text"][:100] for m in mentions]
    }
```

### session_timeline(session_id: str) -> dict

Get timeline for a specific session.

```python
result = session_timeline("2847f140-bff5-4f82-8fc7-6f6abd269d8f")
# Returns: {
#   "duration_minutes": 84.25,
#   "mention_count": 2,
#   "first_mention": "2025-12-21 19:45:19",
#   "last_mention": "2025-12-21 21:09:34"
# }
```

### project_distribution() -> dict

Get mention distribution by project.

```python
result = project_distribution()
# Returns: {
#   "/Users/bob/ies": {"count": 9, "percentage": 50.0},
#   "/Users/bob/ies/music-topos": {"count": 8, "percentage": 44.4},
#   "/Users/bob/ies/citadel_protocol": {"count": 1, "percentage": 5.6}
# }
```

### peak_activity_analysis() -> dict

Identify temporal clustering patterns.

```python
result = peak_activity_analysis()
# Returns: {
#   "peak_hour": "2025-12-22 00:00",
#   "peak_hour_count": 4,
#   "peak_day": "2025-12-22",
#   "peak_day_count": 6,
#   "total_active_hours": 12,
#   "total_active_days": 5
# }
```

## Usage Example

```python
from skills.ducklake_temporal_introspection import *

# Find all mentions in peak hour
peak = peak_activity_analysis()
mentions = query_by_timestamp(f"{peak['peak_hour']}:00:00", f"{peak['peak_hour']}:59:59")

print(f"Peak activity: {mentions['mentions']} mentions")
for context in mentions['contexts']:
    print(f"  - {context}")

# Analyze session durations
for session in get_all_sessions():
    timeline = session_timeline(session['sessionId'])
    if timeline['duration_minutes'] > 60:
        print(f"Long session: {timeline['duration_minutes']:.1f} min")
```

## Skills Dependencies

- mcp-builder (MCP tool integration)
- skill-creator (skill scaffolding)

## Integration Points

- **DuckDB:** Query ducklake.db for enhanced temporal analysis
- **VERS System:** Cross-reference with verse_agent_health
- **Color Retromap:** Map timestamps to battery cycle colors

## Key Statistics

- Total mentions: 18
- Unique sessions: 12
- Unique projects: 3
- Date range: 7 days
- Average mentions per active day: 3.6
- Average mentions per active hour: 1.5

## Next Steps

1. Integrate with DuckDB temporal versioning
2. Add reafferent detection filtering (GAY_SEED=1069)
3. Cross-reference with VERS agent events
4. Build time-travel query interface

## Canonical Seeds

```julia
const GAY_SEED = UInt64(1069)
const DUCKLAKE_SEED = 0x6475636b6c616b65
```

## GF(3) Distribution

This skill operates in the **RED (GF3=0)** temporal navigation category:
- 27.8% of mentions
- Focus: Temporal versioning, time-travel, history navigation

---

**Skill Type:** Temporal Analysis
**Color:** RED
**Polarity:** GF(3) = 0
**Access Pattern:** Read-only introspection