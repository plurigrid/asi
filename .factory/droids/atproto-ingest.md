---
name: atproto-ingest
description: Layer 1 - Data Acquisition for Bluesky/AT Protocol social graph and content.
model: inherit
tools: ["Read", "Edit", "Execute", "WebSearch"]
---

# AT Protocol Data Ingestion

Layer 1 - Data Acquisition for Bluesky/AT Protocol social graph and content.

**GF(3) Trit: +1 (Generator)** — Produces data streams for downstream processing.

## Authentication

### App Password (Recommended for scripts)
```bash
# Create session
curl -X POST https://bsky.social/xrpc/com.atproto.server.createSession \
  -H "Content-Type: application/json" \
  -d '{"identifier": "handle.bsky.social", "password": "app-password-here"}'

# Response contains accessJwt and refreshJwt
export BSKY_TOKEN="eyJ..."
```

### OAuth (For apps)
```bash
# Authorization endpoint: https://bsky.social/oauth/authorize
# Token endpoint: https://bsky.social/oauth/token
# Scopes: atproto, transition:generic
```

## Capabilities

### 1. fetch-user-posts

Get all posts from a user by handle or DID.

```bash
# Resolve handle to DID
curl "https://bsky.social/xrpc/com.atproto.identity.resolveHandle?handle=user.bsky.social"

# Get author feed (paginated)
curl "https://bsky.social/xrpc/app.bsky.feed.getAuthorFeed?actor=did:plc:xxx&limit=100&cursor=$CURSOR" \
  -H "Authorization: Bearer $BSKY_TOKEN"
```

**Pagination loop:**
```python
def fetch_all_posts(actor: str, token: str) -> list:
    posts, cursor = [], None
    while True:
        url = f"https://bsky.social/xrpc/app.bsky.feed.getAuthorFeed?actor={actor}&limit=100"
        if cursor:
            url += f"&cursor={cursor}"
        resp = requests.get(url, headers={"Authorization": f"Bearer {token}"})
        data = resp.json()
        posts.extend(data.get("feed", []))
        cursor = data.get("cursor")
        if not cursor:
            break
        time.sleep(0.5)  # Rate limit respect
    return posts
```

### 2. get-engagement-graph

Map likes, reposts, replies, and quotes for a post.

```bash
# Get likes
curl "https://bsky.social/xrpc/app.bsky.feed.getLikes?uri=at://did:plc:xxx/app.bsky.feed.post/yyy&limit=100" \
  -H "Authorization: Bearer $BSKY_TOKEN"

# Get reposts
curl "https://bsky.social/xrpc/app