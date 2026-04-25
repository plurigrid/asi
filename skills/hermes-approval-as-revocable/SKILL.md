---
name: hermes-approval-as-revocable
description: Replace Hermes' regex-based dangerous-command detector + per-session approval state with a Goblins revocable forwarder — every authority grant has explicit lifecycle (count-limited, time-limited, user-revocable). Approval becomes a cap operation, not a string-pattern guess.
type: bridge
parent: hermes-goblins-bridge
row: 15
proto: R
polarity: -1
status: stub
---

# hermes-approval-as-revocable

Phase 1. Replaces "we hope this regex catches all dangerous commands" with "the LLM literally cannot perform the action without holding an unrevoked cap."

## Hermes signature

`/Users/bob/i/hermes-agent/tools/approval.py`

```python
DANGEROUS_PATTERNS = [(r'\brm\s+...', "recursive delete"), ...]
def detect_dangerous_command(cmd) -> Optional[str]: ...
def is_command_approved(session_key, cmd) -> bool: ...
def approve_command(session_key, cmd, scope='once'|'session'|'permanent'): ...
# Per-session state: contextvars + thread-safe dict, keyed by session_key
```

Approval scopes: `once`, `session`, `permanent` (config.yaml). Smart-approval uses an auxiliary LLM to auto-approve "low-risk" commands.

Authority pattern: **detect-then-prompt**. Regex misses → silent escape. Approval state stored as session-keyed boolean → no built-in expiry, no cap-style attenuation, no propagation across delegation.

## Goblins signature

`/Users/bob/i/goblins-adapter/` — a `^revocable` wrapper around any cap, with explicit lifecycle.

```scheme
(define (^revocable bcom inner-cap
                    #:max-uses (n #f)
                    #:expires-at (deadline #f))
  (define uses 0)
  (define revoked? #f)
  (methods
    (* args
      (when revoked? (raise 'revoked))
      (when (and deadline (> (current-time) deadline)) (raise 'expired))
      (when (and n (>= uses n)) (raise 'exhausted))
      (set! uses (+ uses 1))
      (apply <- inner-cap args)))
  ;; Sealed revoker — only the granter holds it
  (values self (lambda () (set! revoked? #t))))
```

User approval = "give the agent a `^revocable` wrapper around the dangerous cap, hold the revoker yourself." Once-scope = `#:max-uses 1`. Session-scope = revoker dropped at session end. Permanent-scope = unwrapped inner cap (with audit logging).

## Translation table

| Hermes call | Goblins message | Notes |
|---|---|---|
| `detect_dangerous_command(cmd)` | (deleted) | dangerous == "no cap held"; not a string property |
| `approve_command(sk, cmd, 'once')` | `(spawn ^revocable inner #:max-uses 1)` | LLM gets the wrapper; user gets the revoker |
| `approve_command(sk, cmd, 'session')` | `(spawn ^revocable inner)` + drop-at-session-end | session lifecycle = revoker scope |
| `approve_command(sk, cmd, 'permanent')` | grant raw inner cap (with audit forwarder) | persisted in SturdyRef store (`hermes-cred-as-sturdy`) |
| smart-approval (aux LLM) | unchanged — but the LLM-judge produces a *proposed* cap, user-approves | judge cannot grant authority, only request it |
| revoke approval | `(revoker)` thunk | atomic; subsequent calls raise `'revoked` |

## Failure modes (closed by this bridge)

- **Regex misses a dangerous variant** — there are no patterns to miss; lack of cap is what blocks the call.
- **Approval persists past intended scope** — every grant carries explicit `max-uses` / `deadline`; revocation is one thunk call.
- **Approval leaks across sessions** — wrapper is per-spawn; cannot be cloned.
- **Smart-approval LLM judge mistake** — judge can only *request* a wrapper; granting still requires user (or upstream cap-holder) action.
- **Delegated subagent inheriting parent's approvals silently** — caps don't propagate unless explicitly forwarded; see `hermes-delegate-as-spawn` (row 2).

## Failure modes (introduced; must mitigate)

- **Revoker loss** — if the user-side process holding the revoker crashes, cap becomes unrevokable until expiry. → require `#:expires-at` on every grant; no infinite-lifetime caps without re-confirmation.
- **Time-skew on `deadline`** — vat clock vs user clock; use monotonic vat-time + grace window.

## Test vector

```python
# Once-scope:
cap = approve_once(dangerous_op)
cap.invoke(args)            # OK
cap.invoke(args)            # CapError('exhausted')

# Revocation:
cap, revoke = approve_session(dangerous_op)
cap.invoke(args)            # OK
revoke()
cap.invoke(args)            # CapError('revoked')

# Time-limited:
cap = approve_for(dangerous_op, seconds=60)
sleep(61); cap.invoke(args) # CapError('expired')

# Sub-agent isolation:
parent_cap = approve(...)
delegate.spawn(child, caps=[])  # child sees nothing
delegate.spawn(child, caps=[parent_cap])  # explicit forwarding only
```

## Capability diff

| Property | Hermes (status quo) | Goblins (this bridge) |
|---|---|---|
| Authority decision | regex-pattern match | cap presence/absence |
| Granularity | per-command-string | per-cap-reference |
| Expiry | none (or session-scoped) | `max-uses` + `deadline` first-class |
| Revocation | manual session-state edit | one revoker thunk |
| Inheritance to sub-agents | implicit (session_key sharing) | explicit forwarding only |
| Audit | "approved at T" | full call ledger via vat |
| Failure mode | regex-miss = silent escalation | no cap = no call |

## Test-harness location

`~/i/goblins-adapter/tests/revocable-bisim.scm` (todo) — bisim against Python entrypoint shim. Adversarial probe: regex-evading dangerous command (e.g. `r''m -rf /`, unicode-confusable `rm`, indirect via `xargs`) — Hermes may pass, cap version always fails (no cap held).

## Status: stub

Phase 1 priority. Foundational for `hermes-cred-as-sturdy` (row 7) and `hermes-mcp-as-sealed` (row 8) — both build on the revocable-forwarder primitive.
