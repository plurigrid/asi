---
name: bluesky-jetstream
description: Bluesky Jetstream Firehose Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Bluesky Jetstream Firehose Skill

**GF(3) Trit**: -1 (MINUS - validator/filter on incoming data stream)
**Role**: Constrain and validate Bluesky firehose events before processing

## Overview

Jetstream is Bluesky's simplified JSON firehose - a WebSocket streaming API that provides real-time access to all public activity on the Bluesky network. Unlike the full atproto firehose (which uses CBOR/CAR binary encoding), Jetstream delivers plain JSON, making it accessible for rapid prototyping.

**Endpoints**:
- Primary: `wss://jetstream2.us-east.bsky.network/subscribe`
- Backup: `wss://jetstream1.us-west.bsky.network/subscribe`

**Source**: [github.com/bluesky-social/jetstream](https://github.com/bluesky-social/jetstream)

## Query Parameters

| Parameter | Type | Description |
|-----------|------|-------------|
| `wantedCollections` | string[] | Filter by NSID (repeatable) |
| `wantedDids` | string[] | Filter by specific DIDs (repeatable) |
| `compress` | boolean | Enable zstd compression |
| `cursor` | integer | Resume from timestamp (microseconds since epoch) |

Example URL:
```
wss://jetstream2.us-east.bsky.network/subscribe?wantedCollections=app.bsky.feed.post&wantedCollections=app.bsky.feed.like
```

## Message Types

### commit
Repository commit events (most common):
```json
{
  "did": "did:plc:abc123...",
  "time_us": 1703123456789012,
  "kind": "commit",
  "commit": {
    "rev": "3k...",
    "operation": "create",
    "collection": "app.bsky.feed.post",
    "rkey": "3k...",
    "record": {
      "$type": "app.bsky.feed.post",
      "text": "Hello world!",
      "createdAt": "2024-12-21T10:00:00.000Z"
    },
    "cid": "bafyrei..."
  }
}
```

### identity
Identity updates:
```json
{
  "did": "did:plc:abc123...",
  "time_us": 1703123456789012,
  "kind": "identity",
  "identity": {
    "did": "did:plc:abc123...",
    "handle": "alice.bsky.social",
    "seq": 12345
  }
}
```

### account
Account status changes:
```json
{
  "did": "did:plc:abc123...",
  "time_us": 