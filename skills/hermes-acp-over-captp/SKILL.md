---
name: hermes-acp-over-captp
description: Bridge Hermes' ACP (Agent Client Protocol) transport onto OCapN/CapTP for RPC and Syndicate for the registry/presence layer. The dual (R+D) row of the rubric — invocation/response naturally fits CapTP, while session/agent discovery fits Syndicate dataspace facts. Removes ACP's bespoke wire while keeping its ergonomics.
type: bridge
parent: hermes-goblins-bridge
row: 13
proto: R+D
polarity: -1
status: stub
---

# hermes-acp-over-captp

Phase 1 — only "partial" status row in the table; ACP already exists, this bridge re-grounds its transport.

## Hermes signature

`/Users/bob/i/hermes-agent/acp_adapter/` (9 files):

- `server.py` — exposes Hermes via `acp` (Agent Client Protocol) JSON-RPC; handlers for `Initialize`, `NewSession`, `Prompt`, `LoadSession`, `Fork`, `SetSessionModel`, etc.
- `auth.py` — provider detection / API-key auth (`AuthMethodAgent`)
- `session.py` — per-session conversation state, cancellation, mode/model switching
- `events.py` — streaming callbacks (`make_message_cb`, `make_step_cb`, `make_thinking_cb`, `make_tool_progress_cb`)
- `permissions.py` — tool permission gates
- `tools.py` — ACP-side tool surface
- `entry.py` — ACP transport bootstrap (stdio / SSE / HTTP)
- `__main__.py` — CLI entrypoint

ACP itself: open W3C-ish JSON-RPC over stdio/SSE/HTTP, used by Zed and other clients to drive agents. Wire format is its own thing.

Authority pattern: **bearer-token + per-session permission registry** — caller authenticates once, then sends method names; server consults `permissions.py` per call. Discovery (`ListSessions`) is centralized via the server.

## Goblins signature

Two-protocol split, since ACP has both invocation and discovery surfaces:

### R half — RPC over CapTP
`/Users/bob/i/goblins-adapter/` netlayer + Syrup wire format. ACP method calls become eventual sends:

```scheme
;; ACP "Prompt" → CapTP eventual send
(<- session-cap 'prompt content-blocks)
;; ACP "NewSession" → spawn + return ref
(define new-session (spawn ^acp-session #:model model #:tools tools))
;; Streaming events → promise resolutions / channel
```

CapTP gives: promise pipelining (chained ACP calls don't round-trip), three-vat introductions (one ACP client can hand off a session ref to another client without re-auth), persistent SturdyRefs (sessions resumable across reconnects).

### D half — Registry/discovery via Syndicate dataspace
Sessions, agents, model availability published as facts:

```scheme
;; Agent advertises itself
(assert! ds `(agent ,agent-id #:model ,model #:tools ,tool-list))
;; Client subscribes to find sessions
(observe ds `(session ?id #:status active))
;; Session state changes → fact retraction + new assertion
```

`ListSessions`, `SetSessionModel`, model availability — all dataspace observers, not RPC polls.

## Translation table

| ACP method | Goblins fit | Side |
|---|---|---|
| `Initialize` | CapTP handshake + capability exchange | R |
| `Authenticate` | SturdyRef redemption | R |
| `NewSession` | `spawn ^acp-session` returning cap | R |
| `Prompt` | `(<- session 'prompt blocks)` | R |
| `Cancel` | `(revoker)` thunk on session | R |
| `LoadSession` | `(restore-sturdyref id)` | R |
| `ForkSession` | `(<- session 'fork)` returning new cap | R |
| `SetSessionModel` | `(<- session 'set-model m)` + dataspace re-assertion | R + D |
| streaming events | promise resolutions / channel publishing | R |
| `ListSessions` | `(observe ds '(session ?id ...))` | D |
| `ListAgents` (peer discovery) | `(observe ds '(agent ?id ...))` | D |
| permissions registry | revocable forwarders per tool cap | R (see row 15) |

## Failure modes (closed by this bridge)

- **Bearer token reuse / leakage** — replaced by SturdyRefs (unguessable, cap-discipline; revocation drops the forwarder).
- **Centralized session list as single point of trust** — Syndicate dataspace lets each agent assert its own facts; observers see the union, no central authority.
- **Re-auth on reconnect** — SturdyRef restoration is the standard CapTP idiom; no token refresh dance.
- **Cross-client handoff requires sharing the bearer** — three-vat introductions hand off a cap reference without sharing secrets.

## Failure modes (introduced; must mitigate)

- **Dataspace flooding** — a misbehaving agent could flood facts. → rate-limit at netlayer + use revocable observer caps.
- **CapTP↔ACP semantic drift** — ACP clients (Zed, etc.) will not learn CapTP overnight. → keep ACP server as a *thin shim* on top of the CapTP-shaped vat; Zed sees ACP, internals are CapTP.

## Test vector

```python
# Cross-impl bisim probe (Hermes ACP server ↔ Goblins CapTP vat ↔ Troupe-Haskell vat):
# Same prompt sequence, same model, same tools → same observable response stream
# (modulo nondeterminism budgeted by G7 oracle).

# Three-vat introduction:
client_a.create_session() → cap_A
client_a.handoff(cap_A, to=client_b)
client_b.prompt(cap_A, "...")  # works without client_b ever seeing client_a's auth

# Discovery via dataspace:
observer.subscribe('(session ?id #:model "claude-opus-4-7")')
# returns set of currently-active matching sessions, updates as facts churn
```

## Capability diff

| Property | Hermes ACP (status quo) | Hermes-over-CapTP+Syndicate |
|---|---|---|
| Wire format | bespoke JSON-RPC | Syrup (typed, content-addressable) |
| Authority | bearer token | SturdyRef + revocable forwarders |
| Pipelining | request/response | CapTP promise pipelining |
| Cross-client handoff | reshare token (insecure) | three-vat introduction |
| Discovery | server-curated `ListSessions` | Syndicate dataspace observers |
| Reconnect | re-auth + LoadSession | restore SturdyRef |
| Failure mode | token leak = full session takeover | cap revocation atomic |

## Test-harness location

`~/i/goblins-adapter/tests/acp-captp-bisim.scm` (todo). G7 bisim probe set must include: ACP-shim ↔ CapTP-direct call equivalence, three-vat handoff, dataspace-vs-list-sessions equivalence under churn.

## Cross-impl notes

This is one of the strongest rows for Troupe-Haskell as bisim peer (memory `troupe-syndicate-haskell.md`) — both OCapN and Syndicate land together in their NLnet milestones, and ACP is the obvious interop target for a Haskell agent harness.

## Status: ◐ partial → stub of bridge

Phase 1 priority. The R half lands first (ACP→CapTP shim); the D half (registry→dataspace) lands with `hermes-mem-as-dataspace` (row 9) since they share the dataspace primitive.
