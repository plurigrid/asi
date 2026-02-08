---
name: pulse-mcp-stream
description: ' Layer 1: Real-Time Social Stream Monitoring via MCP'
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# pulse-mcp-stream

> Layer 1: Real-Time Social Stream Monitoring via MCP

**Version**: 1.0.0  
**Trit**: +1 (Generator - produces live data)  
**Bundle**: acquisition  

## Overview

Pulse-MCP-stream provides real-time monitoring of social interactions, enabling the cognitive surrogate system to stay updated with the latest patterns. It streams mentions, engagement changes, and trending topics.

## Capabilities

### 1. subscribe-actor

Subscribe to real-time updates for a user.

```python
from pulse_mcp_stream import PulseClient

client = PulseClient(seed=0xf061ebbc2ca74d78)

async for event in client.subscribe_actor("barton.bsky.social"):
    match event.type:
        case "post":
            print(f"New post: {event.text[:50]}...")
        case "reply":
            print(f"Reply from {event.actor}: {event.text[:30]}...")
        case "like":
            print(f"Liked by {event.actor}")
        case "repost":
            print(f"Reposted by {event.actor}")
        case "mention":
            print(f"Mentioned by {event.actor}")
```

### 2. monitor-engagement-delta

Track engagement changes in real-time.

```python
async for delta in client.monitor_engagement_delta("barton.bsky.social"):
    # delta = {
    #   post_id: "at://...",
    #   likes_delta: +5,
    #   reposts_delta: +2,
    #   replies_delta: +1,
    #   timestamp: "2024-12-22T05:00:00Z",
    #   velocity: 2.3  # engagements per minute
    # }
    
    if delta.velocity > 5.0:
        print(f"🔥 Viral post detected: {delta.post_id}")
```

### 3. trend-detect-network

Detect trending topics in a user's network.

```python
trends = await client.trend_detect_network(
    center_user="barton.bsky.social",
    time_window_minutes=60,
    min_mentions=3
)

# Returns:
# [
#   {topic: "category theory", mentions: 12, velocity: 0.2/min},
#   {topic: "Gay.jl", mentions: 8, velocity: 0.13/min},
#   {topic: "MCP servers", mentions: 5, velocity: 0.08/min}
# ]
```

### 4. firehose-filter

Connect to Bluesky firehose