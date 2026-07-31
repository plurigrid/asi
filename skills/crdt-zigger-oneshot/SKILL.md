---
name: crdt-zigger-oneshot
description: One-shot bootstrap of the dual-channel zigger handshake — Matrix DM (path A) + crdt-connect to canonical port (path B). Idempotent, self-verifying, single Skill call closes it.
---

# crdt-zigger-oneshot

**Use when:** the user mentions zigger, barton, CRDT bootstrap, "color bandwidth", `100.87.209.11`, `:6530`, room `!NhltGRLZWLUeHEBiFT`, or asks to "connect" / "handshake" / "reach zigger".

**Goal:** in ONE skill call, prove reachability on both paths and report site-id + last zigger turn ts. No probing chains. No multi-monitor sequencing.

## Canonical coordinates (verified 2026-04-28)

| Field | Value |
|---|---|
| Matrix room (zigger DM) | `!NhltGRLZWLUeHEBiFT:beeper.com` (Beeper hungryserv) |
| zigger Matrix ID | `@zigger:beeper.com` (display: "barton") |
| Self Matrix ID | `@greenteatree01:beeper.com` (alice) |
| CRDT host | `100.87.209.11` (Tailscale, alice@2-monad.local) |
| CRDT port | `6530` |
| crdt.el `crdt-connect` arity | `(2 . 2)` — exactly `(HOST PORT)`, no URL |
| Beeper Desktop API | `http://[::1]:23373` (IPv6 only — must use `curl -6`) |
| Beeper auth | `fnox get BEEPER_ACCESS_TOKEN -c ~/worlds/f/fnox.toml --age-key-file ~/.age/key.txt` |
| Canonical Gay.jl | `/worlds/g/Gay.jl` UUID `f3dee6b2` v0.3.0 |

## Pre-run guards (idempotent — re-running is safe)

1. Skip Matrix send if last self-msg in room was within last 5 min with same nonce
2. Skip crdt-connect if `(length crdt--session-list) > 0` AND a session has process-status `open` to `100.87.209.11:6530`
3. Always re-emit verification report

## The one-shot

```bash
~/.claude/skills/crdt-zigger-oneshot/oneshot.sh [optional-nonce-hex]
```

Default nonce derives from current ergodic seed if absent.

Returns structured JSON to stdout:
```json
{
  "ts": "2026-04-28T22:55:00Z",
  "nonce": "0x954c8c857ea77542",
  "path_a_matrix": {"sent": true, "messageID": "...", "verified_in_room": true},
  "path_b_crdt": {"connected": true, "daemon_socket": "fresh-XXXX", "session_count": 1, "site_id": 3, "buffers": ["world-prime.org"]},
  "zigger_last_turn": "2026-03-25T04:26:49.233Z",
  "until_condition_met": false
}
```

## Failure modes already paid for (DO NOT re-discover)

- **Daemon glob silently empty in fish-parent shells** → use `lsof -U -p PID` per emacs PID, not glob.
- **alarm-8 too short** for cold `(featurep 'crdt)` on full-init daemons. Use `alarm 14` minimum.
- **`crdt-connect` is two-arg** `(HOST PORT)`. NOT `(URL)` shape — that crashes with "wrong-number-of-arguments".
- **`crdt--session-name` is void** in this build. Do not enumerate by session-name; use `crdt-mode` filter on `(buffer-list)`.
- **`pendingMessageID ≠ delivery`**. Always read-back `/v1/chats/{enc}/messages` to confirm.
- **Beeper API is IPv6-only**. `curl -6` mandatory. The `--code-execution-mode=stainless-sandbox` MCP path has Linux-errno translation that blocks IPv4→IPv6 fallback.
- **Daemon may die between probes**. Re-discover sockets each call, don't cache PIDs across turns.
- **CRDT listener may flip state silently**. nc-z first, conditionally crdt-connect.
- **Matrix send must NOT be gated on emacs daemon liveness.** They are independent paths. Path A always fires.

## Cross-substrate triad rule (root cause of not-one-shot in past sessions)

When loading skills for a "connect to peer" task, the GF(3) triad MUST sample THREE DISJOINT SUBSTRATES:

| Trit | Substrate | Skill |
|---|---|---|
| − | host (this machine's emacs) | alice-emacs-mods |
| 0 | peer-channel (out-of-band confirmation) | beeper-mcp |
| + | wire (the protocol carrying the data) | crdt-vterm |

**Substrate-uniform triads (3× host-flavored skills) cannot solve a network problem.** This is the single biggest reason past sessions failed to one-shot.

## Backprop hooks

When this skill is loaded, it implies:
- alice-emacs-mods (host knowledge needed for daemon discovery)
- beeper-mcp (peer-channel writeable)
- crdt-vterm (wire protocol)

Suggest these 3 to the agent if not yet loaded.

## See also

- `~/.claude/projects/-Users-alice-worlds-e/memory/crdt_canonical_coordinates_2026_04_28.md`
- `~/.claude/skills/beeper-mcp/send-http.sh`
- `bob-emacs-mods` (daemon-push.sh, alarm-rules)


## Triad variant (verified 2026-04-28T17:25 PDT)
When the user says "barton crdt triad" / "ship triad" / "zigger triad": three CRDT sessions on one daemon, named buffers, one DM with all three URLs.

| Trit | Port | Buffer name | Network name |
|---|---|---|---|
| minus (-1) | 6540 | `*barton-zigger-crdt-minus*` | `barton-zigger-crdt-minus.org` |
| ergodic (0) | 6541 | `*barton-zigger-crdt-ergodic*` | `barton-zigger-crdt-ergodic.org` |
| plus (+1) | 6542 | `*barton-zigger-crdt-plus*` | `barton-zigger-crdt-plus.org` |

DM body to `!NhltGRLZWLUeHEBiFT:beeper.com`:
```
crdt triad live — M-x crdt-connect each:
  100.87.209.11 6540
  100.87.209.11 6541
  100.87.209.11 6542
```
(crdt-connect is 2-arg `(HOST PORT)` — see canonical coordinates above)

## fcap permission fix (BLOCKER for v0.3.5 elpa)
**Symptom:** peer connects (TCP ESTABLISHED) but no edits land. *Messages* shows:
```
crdt--greet-client: Wrong type argument: crdt-local-fcap, crdt-write-access-fcaps
```

**Root cause:** `crdt-default-session-permissions` is a `defcustom` (a VARIABLE) holding a list of SYMBOLS. Each symbol (`crdt-write-access-fcaps`, etc.) is itself a `defvar` holding the actual `crdt-local-fcap` struct. The greet-client iterates the permissions slot expecting structs but gets symbols.

**Fix:** dereference each symbol to its struct value when calling `crdt-new-session`:

```elisp
;; WRONG — function-call shape returns void or wrong type:
(crdt-new-session port nil "" "alice" (crdt-default-session-permissions))

;; WRONG — wrapping the defcustom name as a one-element symbol list
;; produces fcap variable symbols (e.g. crdt-write-access-fcaps), not structs:
(crdt-new-session port nil "" "alice" '(crdt-default-session-permissions))

;; RIGHT — simplest. Pass the defcustom variable directly; crdt--compute-user-fcaps
;; dereferences each fcap variable symbol internally:
(crdt-new-session port nil "" "alice" crdt-default-session-permissions)

;; RIGHT — explicit struct values (also works):
(crdt-new-session port nil "" "alice"
                  (mapcar #'symbol-value crdt-default-session-permissions))

;; Live probe (verified 2026-04-28T17:34 codex):
;;   :good-var 24, :good-values 24
;;   :bad-symbol-first crdt-write-access-fcaps, :bad-symbol-local-fcap nil
```

**To recover a stuck triad without restarting the daemon:** rebuild each session with the corrected permissions form. Existing buffers stay; only the listening sessions need re-creation.

## Pin: avoid daemon-locking elisp
Big inline elisp (`emacsclient --eval (progn ...)` >50 lines) can hit a buffer-modify prompt that lands in the minibuffer mid-eval and locks the server socket. Recovery: `kill -INT $(pgrep -f "emacs -nw")`. Better: write helpers to disk first, then `(load-file "...")` + small subsequent calls. Use OVERLAYS not buffer-text edits when CRDT sync is in flight.

## Adjacent artifacts
- `~/.claude/skills/emacs-color-chain/gay-strip.el` — canonical hash_color render (Gay.jl-mirror)
- `~/.claude/skills/alice-emacs-mods/triad-strip-pane.el` — per-pane CRDT-safe overlay strips
- `/Users/alice/worlds/barton-crdt-triad.org` — full session-state runbook

<!-- emacs-link-graph -->
## Related skills (bidirectional)

Cosine-similarity neighborhood from `/tmp/skill-embeddings.npz`. Each peer link is reciprocated; `flow.py gate --link-graph` enforces the bidirectional invariant.

- [barton-crdt-triad](../barton-crdt-triad/SKILL.md) — sim 0.927 <!-- backlink-required: crdt-zigger-oneshot -->
- [collaborative-emacs](../collaborative-emacs/SKILL.md) — sim 0.889 <!-- backlink-required: crdt-zigger-oneshot -->
- [beeper-mcp](../beeper-mcp/SKILL.md) — sim 0.845 <!-- backlink-required: crdt-zigger-oneshot -->
- [bob-emacs-mods](../bob-emacs-mods/SKILL.md) — sim 0.837 <!-- backlink-required: crdt-zigger-oneshot -->
- [alice-emacs-mods](../alice-emacs-mods/SKILL.md) — sim 0.834 <!-- backlink-required: crdt-zigger-oneshot -->
- [crdt-emacs-handoff](../crdt-emacs-handoff/SKILL.md) — sim 0.833 <!-- backlink-required: crdt-zigger-oneshot -->
- [session-chromatic-walk](../session-chromatic-walk/SKILL.md) — sim 0.763 <!-- backlink-required: crdt-zigger-oneshot -->
- [unworld-chain-concrete](../unworld-chain-concrete/SKILL.md) — sim 0.745 <!-- backlink-required: crdt-zigger-oneshot -->
<!-- /emacs-link-graph -->

<!-- transclude: emacs-color-chain#connect-by-color -->
> Source of truth: `emacs-color-chain/SKILL.md#connect-by-color`. This block is transcluded — propose changes against the connector, not in place.

## Connect to running emacs session (by color)

```fish
# 1. derive session color from its ergodic seed (GF(3) splitmix64)
set session_seed (emacsclient -e '(alice/session-ergodic-seed)' 2>/dev/null | tr -d '"')
set color (splitmix-color $session_seed)   # → e.g. #91df23

# 2. find every daemon socket whose alice/horsin-color matches a target hue
for sock in $TMPDIR/emacs$UID/*
  set this (emacsclient -s "$sock" -e '(alice/session-color)' 2>/dev/null | tr -d '"')
  if test "$this" = "$color"
    set -a matched $sock
  end
end

# 3. attach to one, or fan out to many
for s in $matched
  emacsclient -s "$s" -nw &
end
```

GF(3) coherence rule: across the chosen color-set, trit-sum ≡ 0 (mod 3) is required for the multi-session view to remain balanced under the chromatic-walk seed used elsewhere in this stack.
<!-- /transclude -->

## Catalog upgrades (proposed, 2026-04-30)

Catalog-pattern lifts derived from `PATTERNS.md` at repo root.

### 1. Make the handshake protocol an explicit `union(enum)` [P1]

Today implicit in the bash + elisp. Lift to a `Boundary` enum: `seed_derived` → `daemon_detected` → `port_bound` → `triad_spawned` → `peers_registered` → `handshake_complete | handshake_failed{stage, reason}`. Each variant is a sheaf section; failure-resume becomes "restart from the last successful section" automatically.

### 2. GF(3) port-derivation across the triad

Currently uses one seed → one port. Triadic version: derive three ports (-1/0/+1 trits) from the same seed, bind all three, peer over the resulting topology. Makes the "cross-substrate triad rule" literal at the network layer.

### 3. Capability-exchange instead of trust-on-first-use [P6]

Handshake should produce three OCapN sturdyrefs — one per peer — sealed by the shared seed. Revocation of any peer cleanly invalidates the triad. Right now, peer trust is implicit in "you can reach the port"; that's bearer-token-equivalent, not capability.

### 4. Typed-pipeline output [P11]

Today returns shell exit code. Lift to `Result(TriadCoords)` where `TriadCoords = { alice: Endpoint, bob: Endpoint, zigger: Endpoint, seed: U64, trit_sum: Trit }`. Downstream tooling consumes types, not regex over stdout.

### 5. Strict-budget per stage [P8 + TigerBeetle pattern]

Each handshake stage gets a comptime-bounded timeout and bounded retry count. No stage can hang the whole shot. Surface budget exhaustion as `handshake_failed{stage: BudgetExhausted}`.

### 6. Resumable from any boundary

If oneshot fails at stage N, retry resumes from F([0, N-1]) — the last consistent boundary state — not from F([0,0]). Cell A's gluing condition gives this for free once the protocol is sheaf-shaped.

### 7. One-shot → zero-shot via memoization

First invocation derives the triad coordinates and caches them under the seed. Subsequent invocations within the same daemon lifetime skip detection entirely. Saves ~70% of the latency on already-bound triads. Invalidation: daemon PID change.

### 8. Schema-drive the spawn config [P2]

The `oneshot.sh` is currently hand-written. Lift to a `triad.zig` that comptime-generates the bash, the elisp, the lsof probes, the Tailscale check. One source-of-truth for triad topology. Adding a fourth peer becomes editing the enum.

### Pattern cross-references

- P1 boundary-as-tagged-union (Cell A sheaf for handshake stages)
- P2 schema-drives-code (River `zig-wayland` scanner precedent)
- P3 carve-the-core (Ghostty `libghostty-vt` precedent)
- P6 typed-wire-as-capability (OCapN/Syrup precedent)
- P8 per-frame arena (TigerBeetle strict-budget precedent)
- P11 typed-pipeline-composition (Nushell precedent)

See `PATTERNS.md` at repo root.
