---
name: drive-acset
description: Google Drive management via DriveACSet schema with GF(3) triadic routing. Transforms files/folders into typed Interactions, routes to queue fibers, detects saturation for organized-drive-as-condensed-state.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Drive ACSet Skill

Transform Google Drive into a GF(3)-conserving algebraic database system.

**Trit**: 0 (ERGODIC - coordinator)  
**Principle**: Organized Drive = Condensed State  
**Implementation**: DriveACSet + TriadicQueues + SaturationDetector

## DriveACSet Schema

```
┌────────────────────────────────────────────────────────────────────┐
│                       DriveACSet Schema                            │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  File ──────────┬────▶ Folder                                     │
│  ├─ file_id     │      ├─ folder_id: String                       │
│  ├─ name        │      ├─ name: String                            │
│  ├─ mime_type   │      └─ parent ─────────▶ Folder (self-ref)     │
│  ├─ size        │                                                  │
│  └─ parent ─────┘                                                  │
│                                                                    │
│  Permission ────┬────▶ File | Folder                              │
│  ├─ role        │      ├─ reader | commenter | writer | owner     │
│  └─ share_with ─┼──▶   └─ email | domain | anyone                 │
│                 │                                                  │
│  Revision ──────┼────▶ File                                       │
│  ├─ rev_id      │      ├─ modified_time                           │
│  └─ modified_by ┘      └─ keep_forever: Bool                      │
│                                                                    │
│  QueueItem ─────┼────▶ Agent3                                     │
│  ├─ interaction │      ├─ fiber: Trit {-1, 0, +1}                 │
│  └─ agent ──────┘      └─ name: String                            │
└────────────────────────────────────────────────────────────────────┘
```

### Objects

| Object | Description | Trit Role |
|--------|-------------|-----------|
| `File`