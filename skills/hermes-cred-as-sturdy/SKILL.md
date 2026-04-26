---
name: hermes-cred-as-sturdy
description: Replace Hermes' multi-credential pool (raw API keys in process memory + file store) with persistent OCapN SturdyRefs wrapped in revocable forwarders. Each provider key becomes an unguessable, revocable cap reference; rotation = swap forwarder; the LLM never sees the bearer string.
type: bridge
parent: hermes-goblins-bridge
row: 7
proto: R
polarity: 0
status: stub
---

# hermes-cred-as-sturdy

Phase 2 (state). Foundation for `hermes-mcp-as-sealed` and any cap that needs cross-session persistence.

## Hermes signature

`/Users/bob/i/hermes-agent/agent/credential_pool.py` + `hermes_cli/auth.py`

```python
PROVIDER_REGISTRY            # provider → key-shape, base-url, refresh path
read_credential_pool() / write_credential_pool()
_load_provider_state() / _save_provider_state()
# Codex tokens: _import_codex_cli_tokens, _codex_access_token_is_expiring
# Locking: _auth_store_lock (threading.Lock around the file)
```

`run_agent.py:5128,5155` — `_rotate_credential` / `_swap_credential` mid-conversation.

Authority pattern: **bearer-key-in-memory**. Pool is a list of `(provider, key, status, ttl)` tuples. Rotation = pick the next non-rate-limited entry. Persistence = JSON file with file-lock. The agent process holds raw API keys in memory; any tool that imports `credential_pool` can read them.

## Goblins signature

Each credential becomes a **SturdyRef** (unguessable persistent URI) pointing to a `^provider-cap` actor; the actor wraps the raw key and exposes the provider's API methods. Pool = collection of revocable forwarders.

```scheme
;; One provider cap per (provider, key)
(define (^provider-cap bcom provider raw-key base-url)
  (methods
    ((complete prompt opts) (httpx-post base-url 'completions ...))
    ((stream prompt opts)   ...)))

;; Pool wraps each in a revocable forwarder; rotation = move to next un-revoked entry
(define (^cred-pool bcom)
  (define entries (gset))   ; Mandy Pattern D
  (methods
    ((acquire provider)
     (find-active-forwarder entries provider))
    ((rotate provider reason)
     (revoke-current entries provider reason)
     (next entries provider))
    ((add provider sref)    (assert! entries `(cred ,provider ,sref)))
    ((revoke sref)          ((retract-revoker entries sref)))))
```

Persistence via Goblins `vat-snapshot`/`vat-restore` (Mandy Pattern D — `bcom`+`gset`). Raw keys never leave the vat that constructed them.

## Translation table

| Hermes call | Goblins message | Notes |
|---|---|---|
| `read_credential_pool()` | `(<- pool 'list)` | returns SturdyRef list, never raw keys |
| `write_credential_pool(...)` | `(<- pool 'add provider sref)` | new cap spawned, SturdyRef minted |
| `_rotate_credential(provider)` | `(<- pool 'rotate provider 'rate-limit)` | revokes current, returns next forwarder |
| `_swap_credential(...)` | revoke + add | atomic; in-flight requests fail with `'revoked` not 401 |
| `key.is_expiring()` (Codex) | `(<- cred 'expires-at)` + auto-refresh fiber | refresh runs in vat, key never on the wire |
| import API key from env | mint SturdyRef once, store in SturdyRef store; delete env | one-time bootstrap |

## Failure modes (closed by this bridge)

- **Raw key in process memory readable by any tool** — keys live in the provider-cap vat; other vats see only the SturdyRef (URI; useless without the cap-holder vat alive).
- **Key leaks into LLM context via error message** — provider-cap formats errors with redacted refs (`<cred:abc123>`) not raw bytes.
- **Stale rotation race** — Hermes rotates by mutating shared dict; cap version uses revoker thunk → in-flight calls fail atomically with `'revoked`, not by silently using the new key.
- **Cross-session leakage** — SturdyRef is the only persistent handle; restoration requires holding the SturdyRef *and* an unsealer (Mandy Pattern B-style nonce).

## Failure modes (introduced; must mitigate)

- **SturdyRef store leak = full takeover** — store is the equivalent of the Codex token JSON; protect with same OS perms, optionally seal with a passphrase-derived sealer.
- **Refresh-fiber stall** — if the in-vat refresh fiber crashes, cap goes stale. → use Mandy Pattern A `syscaller-free-fiber` for the refresh I/O so the vat queue isn't blocked.

## Test vector

```python
sref = pool.add('anthropic', mint_sturdy(raw_key))
# Raw key never returned again:
assert pool.list() == [{'provider': 'anthropic', 'sref': '<sturdy:abc...>'}]
cap = pool.acquire('anthropic')
cap.complete("hello")        # works
pool.rotate('anthropic', 'rate-limit')
cap.complete("hello")        # CapError('revoked'), not 429
new_cap = pool.acquire('anthropic')
new_cap.complete("hello")    # works on next entry

# Cross-restart:
vat_save(); restart()
pool2 = vat_restore()
pool2.acquire('anthropic')   # works — SturdyRef redeemed
```

## Capability diff

| Property | Hermes (status quo) | Goblins (this bridge) |
|---|---|---|
| Key visibility | any importer of credential_pool | provider-cap vat only |
| Rotation atomicity | dict mutation | revoker thunk → in-flight fail atomically |
| Persistence | JSON + file-lock | SturdyRef + vat-snapshot |
| Refresh | thread + skew check | in-vat fiber, syscaller-free for I/O |
| Audit | log on rotate | every `<-` traversal in vat ledger |
| Failure mode | logger.warning leaks key prefix | `<cred:abc>` opaque ref |

## Test-harness location

`~/i/goblins-adapter/tests/cred-sturdy-bisim.scm` (todo). G7 bisim probe: same prompt sequence to Hermes pool vs Goblins pool, compare provider-side request signatures (modulo timing).

## Status: stub

Phase 2 priority. Blocks `hermes-mcp-as-sealed` (row 8) — MCP OAuth tokens are credentials with extra count-limited semantics, layered on top.
