---
name: crdt-vterm
description: Collaborative terminal session sharing using CRDT-style s-expressions
  with GF(3) trifurcated conflict resolution.
metadata:
  trit: 0
---

# CRDT-VTerm - Collaborative Terminal Sharing

Collaborative terminal session sharing using CRDT-style s-expressions with GF(3) trifurcated conflict resolution.

## Components

### Emacs Bridge
- **File**: `crdt-vterm-bridge.el`
- **Purpose**: Connect vterm.el to crdt.el via shadow buffers

### Babashka Recorder
- **File**: `vterm_crdt_recorder.bb`
- **Purpose**: Record/replay terminal sessions as CRDT sexps

### P2P Sharing
- **File**: `vterm_localsend_share.bb`  
- **Purpose**: Live terminal sharing via localsend multicast

## Architecture

```
┌──────────────────────────────────────────────────────────────────┐
│                    CRDT-VTerm System                             │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────┐     remote-insert     ┌───────────────┐             │
│  │ vterm   │ ───────────────────▶  │ shadow buffer │             │
│  │  PTY    │      (GF3 trit)       │  (crdt.el)    │             │
│  └────┬────┘                       └───────┬───────┘             │
│       │                                    │                     │
│       │ script(1)                          │ sexp file           │
│       ▼                                    ▼                     │
│  ┌─────────┐                       ┌───────────────┐             │
│  │ raw log │                       │ .sexp log     │             │
│  └────┬────┘                       └───────┬───────┘             │
│       │                                    │                     │
│       │ vterm_crdt_recorder.bb             │ localsend UDP       │
│       ▼                                    ▼                     │
│  ┌─────────────────────────────────────────────────┐             │
│  │              P2P Peer Network                   │             │
│  │  ┌───────┐   ┌───────┐   ┌───────┐              │             │
│  │  │ MINUS │   │ERGODIC│   │ PLUS  │  ← GF(3)     │             │
│  │  └───────┘   └───────┘   └───────┘    routing   │             │
│  └─────────────────────────────────────────────────┘             │
└──────────────────────────────────────────────────────────────────┘
```

## CRDT Sexp Format

```clojure
;; Session header
(crdt-terminal-session
  (version "0.1.0")
  (session-id "T-abc123")
  (site-id 42)
  (gf3-assignment :ERGODIC))

;; Terminal output
(remote-insert "0a1b2c3d" 42 "$ ls -la\n"
  (props :type :terminal-output
         :trit :MINUS
         :timestamp 1234567890))

;; User input
(remote-input "0a1b2c3e" 42 "ls -la"
  (props :trit :PLUS
         :timestamp 1234567891))

;; Conflict resolution
(conflict-resolution
  :type :concurrent-input
  :strategy :gf3-ordering)
```

## Usage

### Record Session
```bash
bb vterm_crdt_recorder.bb record session.sexp
```

### Replay Session
```bash
bb vterm_crdt_recorder.bb replay session.sexp 2.0
```

### Live P2P Share
```bash
bb vterm_localsend_share.bb share output.sexp 192.168.1.5
```

### Emacs Replay
```elisp
M-x crdt-vterm-replay RET session.sexp RET 1.0 RET
```

## GF(3) Trifurcated Input

Multi-user input is routed through three queues:

| Queue | Trit | Processing Order |
|-------|------|------------------|
| MINUS | -1 | First |
| ERGODIC | 0 | Second |
| PLUS | +1 | Third |

This prevents conflicts in "no-longer-optimistic waiting" scenarios by deterministically ordering concurrent inputs.

```elisp
;; Cycle through queues
(crdt-vterm-trifurcate-cycle)
```

## Integration

### With gay-mcp
Each terminal session gets a deterministic color based on session ID.

### With localsend-mcp
P2P discovery and file transfer for session sharing.

### With duckdb-ies
Terminal sessions can be indexed in DuckDB for time-travel queries.

## Related Skills
- `gay-mcp` - Deterministic colors
- `spi-parallel-verify` - GF(3) conservation
- `triad-interleave` - Three-stream scheduling
- `bisimulation-game` - Session equivalence

## Catalog upgrades (proposed, 2026-04-30)

Catalog-pattern lifts derived from `PATTERNS.md` at repo root.
Aspirational; current implementation is the bb + .el bridge.

### 1. Boundary-as-tagged-union, not byte-as-CRDT-element [P1]

Stop CRDT-merging the byte stream of the terminal; CRDT-merge the **boundaries** of each command (OSC 133 ;A/;B/;C/;D points). Inside an interval the byte stream is owned by the originator; across intervals the sheaf gluing F([a,b]) = F([a,p]) ×_{F([p,p])} F([p,b]) gives principled three-way merge with no merge conflicts inside running command output. Closes the "two users typed and the output got interleaved" failure mode at the source.

### 2. Capability-sign every op [P6]

Each CRDT operation is a Syrup record sealed by the originator's OCapN sturdyref. No-cloning at op-level: a malicious peer cannot replay another peer's op as their own. Closes trust-on-first-use; combined with OCapN revocation, removing a peer cleanly invalidates pending ops.

### 3. Schema-drive the op set [P2]

Define operations as a `union(enum)` once; comptime-generate (a) the wire codec, (b) the merge function, (c) the elisp bridge, (d) the JSON schema. Removes hand-maintained .el ↔ .bb sync. Adding a new op (e.g., `mark_artifact{id, payload}` for inline images) becomes one enum line.

### 4. Sort-middle compaction for divergent histories [P5]

When peer histories diverge by thousands of ops (long disconnect + re-attach), sort by causal frontier → bin by terminal region → coarse-merge per region → fine-rasterise. Vello-shaped pipeline gives O(n log n) merge with bounded memory.

### 5. Three-way GF(3) merge native

Currently pairwise. Lift to native three-stream merge with sum-to-zero invariant as the consistency check. Any three histories where trit_sum mod 3 ≠ 0 = divergence flag, surfaced in the header line. **A CRDT that lights up red when consensus has actually broken**, instead of silently merging anyway.

### 6. Linear types for one-shot ops

Some ops are measurement-once: confirmations, paste-of-secret, password-prompt acknowledgement. Mark with a Zig-comptime no-clone discipline (or Dafny annotation) so the CRDT layer enforces single-unsealing across all peers. Bridges to entangled-terminal protocols (categorical-quantum-mechanics base-change of D in Cell A).

### 7. Carve `libcrdt-vterm` C ABI [P3]

Today emacs-coupled. Expose `crdt_vterm_new`, `crdt_vterm_apply_op`, `crdt_vterm_export`, `crdt_vterm_subscribe` as C symbols so ghostty, rio, xterm.js, wave can each be a host of the same CRDT engine. Same pattern as ghostty's `libghostty-vt`.

### Pattern cross-references

- P1 boundary-as-tagged-union (Cell A sheaf condition)
- P2 schema-drives-code (Ghostty `parse_table.zig` precedent)
- P3 carve-the-core (`libghostty-vt` precedent)
- P5 sort-middle compute (Vello precedent)
- P6 typed-wire-as-capability (OCapN/Syrup precedent)
- P11 typed-pipeline-composition (Nushell precedent)

See `PATTERNS.md` at repo root.
