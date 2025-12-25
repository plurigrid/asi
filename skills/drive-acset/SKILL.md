---
name: drive-acset
description: Google Drive management via DriveACSet schema with GF(3) triadic routing. Transforms files/folders into typed Interactions, routes to queue fibers, detects saturation for organized-drive-as-condensed-state.
geodesic: true
moebius: "μ(n) ≠ 0"
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
| `File` | Drive file with metadata | Data |
| `Folder` | Hierarchical container | Aggregate |
| `Permission` | ACL entry for sharing | Edge |
| `Revision` | File version history | Temporal |
| `Agent3` | Queue fiber (MINUS/ERGODIC/PLUS) | Router |
| `QueueItem` | Links Interaction → Agent3 | Edge |

## GF(3) Verb Typing

Drive operations assigned trits by information flow:

```python
VERB_TRIT_MAP = {
    # MINUS (-1): Read/Validate
    "get": -1,        "search": -1,    "list": -1,
    "download": -1,   "get_content": -1,
    
    # ERGODIC (0): Coordinate/Permissions
    "share": 0,       "permissions": 0, "move": 0,
    "rename": 0,      "update_metadata": 0,
    
    # PLUS (+1): Create/Execute
    "create": +1,     "upload": +1,    "copy": +1,
    "export": +1,     "transfer_ownership": +1,
}
```

### MCP Tool → Trit Mapping

| Tool | Trit | Description |
|------|------|-------------|
| `search_drive_files` | -1 | Search files (MINUS) |
| `get_drive_file_content` | -1 | Read file (MINUS) |
| `list_drive_items` | -1 | List folder (MINUS) |
| `get_drive_file_permissions` | -1 | Check perms (MINUS) |
| `share_drive_file` | 0 | Share file (ERGODIC) |
| `update_drive_permission` | 0 | Modify perms (ERGODIC) |
| `update_drive_file` | 0 | Update metadata (ERGODIC) |
| `create_drive_file` | +1 | Create file (PLUS) |
| `transfer_drive_ownership` | +1 | Transfer owner (PLUS) |

## Triadic Queue Routing

```
                    ┌─────────────────────────────────────────┐
                    │         DRIVE TRIADIC QUEUES            │
                    ├─────────────────────────────────────────┤
                    │                                         │
   DriveAction ────▶│  route(trit) ───▶ Agent3 Fiber         │
                    │                                         │
                    │  MINUS (-1)  ────▶ [get, search, list]  │
                    │  ERGODIC (0) ────▶ [share, permissions] │
                    │  PLUS (+1)   ────▶ [create, upload]     │
                    │                                         │
                    └─────────────────────────────────────────┘
```

## Saturation Detection

```python
def is_drive_saturated(folder_id: str) -> bool:
    """Folder saturated when:
    1. All files have stable permissions
    2. No pending changes in window N
    3. GF(3) cycle closure: sum(trits) ≡ 0 (mod 3)
    """
    history = detector.history[folder_id][-N:]
    cycle_sum = sum(t for t in folder.gf3_cycle[-3:])
    
    return (
        all(s == history[0] for s in history) and
        (cycle_sum % 3) == 0
    )

def detect_organized_state() -> Dict:
    """Drive at condensed state when:
    1. All folders saturated
    2. Permission graph stable
    3. GF(3) conserved globally
    """
    return {
        "organized": all_saturated and gf3_conserved,
        "condensed_fingerprint": sha256(sorted_file_tree),
    }
```

## Source Files

| File | Description | Trit |
|------|-------------|------|
| [drive_acset.py](file:///Users/alice/agent-o-rama/agent-o-rama/src/drive_acset.py) | ACSet schema + hierarchy | 0 |
| [drive_mcp_bridge.py](file:///Users/alice/agent-o-rama/agent-o-rama/src/drive_mcp_bridge.py) | MCP tool wiring | 0 |
| [permission_graph.py](file:///Users/alice/agent-o-rama/agent-o-rama/src/permission_graph.py) | ACL graph analysis | -1 |

## Workflows

### Workflow 1: Organize Folder to Condensed State

```python
from drive_mcp_bridge import create_drive_bridge
from drive_acset import DriveACSet

bridge = create_drive_bridge("user@gmail.com")
acset = DriveACSet()

# MINUS: List and analyze
items = bridge.list_drive_items(folder_id="root")
for item in items:
    acset.add_file(item) if item.is_file else acset.add_folder(item)

# ERGODIC: Normalize permissions
for file in acset.files_needing_permission_fix():
    bridge.share_drive_file(file.id, share_with="team@domain.com", role="reader")

# PLUS: Create missing structure
bridge.create_drive_file(file_name="README.md", folder_id=folder_id, content="# Index")
```

### Workflow 2: Permission Audit with GF(3) Guard

```python
# MINUS: Check permissions
perms = bridge.get_drive_file_permissions(file_id)

# ERGODIC: Update if needed (requires prior MINUS)
if needs_update(perms):
    bridge.update_drive_permission(file_id, permission_id, role="commenter")

# Verify GF(3) balance
assert acset.gf3_residue() == 0
```

### Workflow 3: Batch File Organization

```python
batch = create_triadic_batch(
    payloads=["list_root", "share_docs", "create_index"],
    folder_id="team_folder",
    seed=1069
)

for interaction in batch:
    system.enqueue(interaction)

stats = system.full_statistics()
print(f"GF(3) Residue: {stats['gf3_residue']}")  # 0
```

## Integration with Other Skills

| Skill | Trit | Integration |
|-------|------|-------------|
| [google-workspace](file:///Users/alice/.claude/skills/google-workspace/SKILL.md) | 0 | MCP tool provider |
| [gmail-anima](file:///Users/alice/agent-o-rama/agent-o-rama/.agents/skills/gmail-anima/SKILL.md) | 0 | Cross-product via attachments |
| [gay-mcp](file:///Users/alice/.agents/skills/gay-mcp/SKILL.md) | +1 | SplitMixTernary RNG |
| [sheaf-cohomology](file:///Users/alice/.claude/skills/sheaf-cohomology/SKILL.md) | -1 | H¹ obstruction on folder tree |

### GF(3) Triadic Conservation

```
drive-acset (0) ⊗ search (-1) ⊗ create (+1) = 0 ✓
get (-1) ⊗ share (0) ⊗ upload (+1) = 0 ✓
list (-1) ⊗ permissions (0) ⊗ copy (+1) = 0 ✓
```

---

**Skill Name**: drive-acset  
**Type**: File Management / ACSet Framework  
**Trit**: 0 (ERGODIC - coordinator)  
**GF(3)**: Conserved via triadic queue routing  
**Principle**: Organized Drive = Condensed State

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
