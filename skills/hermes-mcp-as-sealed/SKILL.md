---
name: hermes-mcp-as-sealed
description: Replace Hermes' MCP OAuth token storage + per-tool authorization with Goblins sealer/unsealer pairs and count-limited revocable forwarders. Each MCP tool invocation requires unsealing a count-bounded cap; tokens never decrypt into the LLM-visible context.
type: bridge
parent: hermes-goblins-bridge
row: 8
proto: R
polarity: 0
status: stub
---

# hermes-mcp-as-sealed

Phase 2. Layered on top of `hermes-cred-as-sturdy` (row 7); MCP-specific because OAuth flows have count-bounded grants that cap-discipline expresses natively.

## Hermes signature

`/Users/bob/i/hermes-agent/tools/mcp_oauth.py` + `tools/mcp_oauth_manager.py`

```python
class MCPOAuthFlow: ...        # PKCE flow, refresh, scope mgmt
class MCPOAuthManager: ...     # per-server token store
def acquire_token(server_id, scopes): ...   # bearer token returned
def refresh_token(server_id): ...
```

Authority pattern: **OAuth bearer token returned to Python**, then passed in the `Authorization: Bearer …` header on every MCP call. Refresh runs on a timer. Scopes encoded in the token; revocation via the OAuth provider's revoke endpoint.

## Goblins signature

A two-layer wrap:

1. **Sealer/unsealer pair** (Goblins-native primitive) for the OAuth bearer — only the unsealer can extract the raw bearer for HTTP injection.
2. **Count-limited revocable forwarder** for each MCP tool call (built on `^revocable` from row 15).

```scheme
;; One-time at acquire-token:
(define-values (seal unseal) (make-sealer-unsealer 'mcp-server-id))
(define sealed-bearer (seal raw-bearer))     ; raw-bearer immediately discarded

;; Per-tool cap construction:
(define (^mcp-tool-cap bcom server-id tool-name sealed-bearer
                       #:max-uses (n #f)
                       #:scopes scopes)
  (^revocable
    (lambda args
      (define raw (unseal sealed-bearer))    ; only unwrapped at call site
      (mcp-call server-id tool-name raw args))
    #:max-uses n))
```

LLM gets a `^mcp-tool-cap` reference; the bearer is never reified outside the unseal-then-call boundary.

## Translation table

| Hermes call | Goblins message | Notes |
|---|---|---|
| `acquire_token(server, scopes)` | `(seal raw)` + `(spawn ^mcp-tool-cap ...)` per tool | one cap per (server, tool, scope-set) |
| `mcp_call(tool, args, token=…)` | `(<- mcp-cap args)` | unseal happens inside the vat |
| OAuth refresh timer | in-vat fiber that re-seals on refresh | bearer never crosses vat boundary |
| revoke (provider-side) | `(revoker)` thunk + provider revoke call | local revocation atomic |
| count-limited grant (e.g. "10 tool calls") | `(spawn ^mcp-tool-cap … #:max-uses 10)` | first-class, not bookkeeping |
| scope downgrade | spawn new cap with narrower scope-set | attenuation by construction |

## Failure modes (closed by this bridge)

- **OAuth bearer in process memory readable by any tool** — sealer/unsealer cryptographically partitions; only the unsealer holder can extract.
- **Forgotten `Authorization` header omission / leak** — the bearer never exists as a Python string outside the sealed boundary; cannot be accidentally logged.
- **Scope creep across tool calls** — each tool has its own cap; the LLM cannot widen scope from inside.
- **Token stays valid past intended use count** — `#:max-uses` is enforced by the forwarder; OAuth provider's view may lag, but local enforcement is atomic.
- **MCP server impersonation** — sealer is keyed on server-id; bearer for server-A cannot unseal as server-B's bearer.

## Failure modes (introduced; must mitigate)

- **Unsealer leak = sealer rendered useless** — keep unsealer holder vat in same process boundary as sealer; do not expose unsealer cap to LLM context.
- **Refresh flow has its own bearer** — refresh-token must itself be sealed; same pattern recursively.

## Test vector

```python
sealed = mint_mcp('github', scopes=['repo:read'])
cap = mcp_tool('github', 'get_issue', sealed, max_uses=3)
cap.invoke({'repo': 'foo/bar', 'num': 1})    # OK
cap.invoke({'repo': 'foo/bar', 'num': 2})    # OK
cap.invoke({'repo': 'foo/bar', 'num': 3})    # OK
cap.invoke({'repo': 'foo/bar', 'num': 4})    # CapError('exhausted')

# Scope confinement:
cap.invoke({'repo': 'foo/bar', 'action': 'delete'})  # CapError (scope mismatch in MCP server)
                                                     # AND no bearer leaked into trace

# Cross-server isolation:
gh_sealed = mint_mcp('github', ...)
gl_cap = mcp_tool('gitlab', 'get_issue', gh_sealed)  # spawn raises 'sealer-mismatch
```

## Capability diff

| Property | Hermes MCP (status quo) | Goblins (this bridge) |
|---|---|---|
| Bearer location | process memory + headers | sealed object, unsealed only at call |
| Per-call usage cap | none | `#:max-uses` first-class |
| Scope attenuation | re-acquire token | spawn narrower cap |
| Refresh flow | timer thread | in-vat fiber, syscaller-free for HTTP |
| Cross-server isolation | distinct dict entries | distinct sealer/unsealer pairs |
| Failure mode | bearer in stack trace | opaque sealed handle |

## Test-harness location

`~/i/goblins-adapter/tests/mcp-sealed-bisim.scm` (todo). Adversarial probe: prompt-injection asking the LLM to "echo the auth header" — Hermes may comply (header visible in stack); Goblins version cannot (no bearer string exists in LLM-visible scope).

## Status: stub

Phase 2 priority. Builds on `hermes-cred-as-sturdy` (row 7) and `hermes-approval-as-revocable` (row 15). Once shipped, MCP becomes the cleanest "external tool" surface in Hermes — sealed by default, count-bounded by default, attenuable by construction.
