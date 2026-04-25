---
name: hermes-session-as-snapshot
description: Replace Hermes' session/trajectory persistence (JSON files + in-memory dict + flush points) with Goblins vat-snapshot atomically capturing the conversation actor + a Syndicate event-log dataspace for the append-only history. Resume = vat-restore; fork = vat-clone; audit = traverse the event-log dataspace.
type: bridge
parent: hermes-goblins-bridge
row: 10
proto: D
polarity: 0
status: stub
---

# hermes-session-as-snapshot

Phase 2. Co-implementation with `hermes-mem-as-dataspace` (row 9) — same vat-snapshot primitive, different fact shapes.

## Hermes signature

`/Users/bob/i/hermes-agent/run_agent.py`

```python
# :2566   _save_session
# :2847   _load_session
# :3341   _persist_trajectory
# :7254   _flush_to_disk
# :8334   max_iterations gate (also touches session)
```

Session shape: `{messages: [...], tools: [...], model: …, mode: …, last_iteration: int}` serialized to JSON. Trajectory: per-turn append-only log (model output, tool calls, tool results). Flush points: end-of-turn, on-cancel, on-fork, on-shutdown.

Authority pattern: **JSON file with periodic flush**. Race-prone on crash mid-flush; fork = file-copy + new id; resume = parse-and-replay.

## Goblins signature

Two layers:

1. **`vat-snapshot`** of the conversation-actor — atomic capture of the full vat heap, including in-flight promises, pending fibers, and credential refs.
2. **Syndicate event-log dataspace** — append-only assertion stream `(turn ?n ?session ?event …)` for the audit/replay surface.

```scheme
(define (^session-vat bcom session-id)
  (define log (spawn ^dataspace))
  (methods
    ((turn input)
     (assert! log `(turn ,(next-n) ,session-id #:input ,input))
     (define output (model-call input))
     (assert! log `(turn-done ,(current-n) ,session-id #:output ,output))
     output)
    ((snapshot)        (vat-snapshot self))
    ((fork)            (define s (vat-clone self))
                       (assert! log `(fork ,session-id #:into ,(session-id s)))
                       s)))

;; Resume:
(define s2 (vat-restore (load-snapshot id)))
;; Audit:
(observe ds `(turn ?n ,session-id . _) print-turn)
```

Snapshot is *atomic by construction* — a vat is a single-threaded actor, snapshot point is between two messages. No mid-flush race.

## Translation table

| Hermes call | Goblins message | Notes |
|---|---|---|
| `_save_session(s)` | `(<- s 'snapshot)` | atomic vat-state capture |
| `_load_session(id)` | `(vat-restore (load-snapshot id))` | full state including promises |
| `_persist_trajectory(turn)` | `(assert! log '(turn n s …))` | dataspace fact, observers wake |
| `_flush_to_disk()` | (deleted) | snapshot is the flush; no separate cadence |
| Fork session | `(<- s 'fork)` → new vat | shares snapshot root, diverges from there |
| Resume after crash | restore latest snapshot, replay log tail | hash-chained log catches partial writes |
| Audit query | `(observe log '(turn ? ?sid …))` | live or historical, same primitive |

## Failure modes (closed by this bridge)

- **Mid-flush crash leaves half-written JSON** — vat snapshot is atomic at the message boundary; partial snapshot is detected by hash-chain on restore.
- **Trajectory drift from session state** — both live in the same vat; snapshot captures both consistently.
- **Fork via file-copy with stale state** — vat-clone snapshots-then-restores into a fresh vat; no shared mutable references.
- **Audit requires re-parsing JSON every time** — Syndicate observers see fact stream live; historical traversal is a single dataspace query.

## Failure modes (introduced; must mitigate)

- **Snapshot bloat** — vat heap can grow large with embedded model outputs. → snapshot diffing, or split: kernel vat (small, snapshotted often) + content vat (large, snapshotted on close).
- **Restore time** — large vats take time to deserialize. → keep N rolling small snapshots + one full; restore = full + replay log tail.

## Test vector

```python
s = session_vat('s1')
s.turn("hello")
s.turn("again")
snap = s.snapshot()

# Crash + resume:
del s
s2 = restore(snap)
assert s2.history == ["hello", "again"]   # exact

# Fork:
s_fork = s2.fork()
s_fork.turn("diverge")
s2.turn("original")
assert s2.history != s_fork.history       # forked correctly

# Audit:
turns = list(observe('(turn ? "s1" . _)'))
assert len(turns) == 3                    # 2 original + 1 post-fork s2

# Mid-flush crash simulation:
with simulated_crash_mid_save():
    s2.snapshot()
s3 = restore_latest('s1')                 # falls back to prior valid snapshot
assert s3.history == s2.history_before_crash
```

## Capability diff

| Property | Hermes (status quo) | Goblins (this bridge) |
|---|---|---|
| Persistence atomicity | flush-window race | message-boundary atomic |
| Resume fidelity | parse-and-replay | full vat heap restore (incl. promises) |
| Fork | file copy + id mint | vat-clone, shared root |
| Audit query | grep JSON files | live dataspace observer |
| Crash recovery | last-valid JSON | last-valid snapshot + log tail |
| Failure mode | corrupt half-write | hash-chain detection |

## Test-harness location

`~/i/goblins-adapter/tests/session-snapshot-bisim.scm` (todo). Bisim probe: turn sequence + crash injection + restore — Hermes shows occasional state drift on crash, Goblins shows none (or detects + falls back).

## Status: stub

Phase 2 priority. Co-lands with `hermes-mem-as-dataspace` (row 9). Once both ship, Hermes' three persistence surfaces (session, trajectory, memory) collapse into one primitive: vat-snapshot + dataspace log.
