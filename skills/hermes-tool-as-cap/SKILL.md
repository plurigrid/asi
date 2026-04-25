---
name: hermes-tool-as-cap
description: Replace Hermes' singleton ToolRegistry (name → handler dispatch with ambient authority) with Goblins vats-with-methods. Each tool becomes an actor; the LLM sees an unguessable URL handle (Mandy nonce-registry pattern); invocation = eventual send. No raw cap leaks into model context.
type: bridge
parent: hermes-goblins-bridge
row: 1
proto: R
polarity: +1
status: stub
---

# hermes-tool-as-cap

Phase 3 (action). The most-used row — every tool call goes through this primitive.

## Hermes signature

`/Users/bob/i/hermes-agent/tools/registry.py`

```python
class ToolEntry:                       # :75
    name, toolset, schema, handler, check_fn,
    requires_env, is_async, description, emoji, max_result_size_chars

class ToolRegistry:                    # :99
    _tools: Dict[str, ToolEntry]
    _toolset_checks: Dict[str, Callable]
    _lock: threading.RLock              # MCP dynamic refresh
    def dispatch(self, name, args): ...   # :291
```

`run_agent.py:7660 _execute_tool_calls_concurrent`, `:7525 _execute_tool_calls`, `:327 _paths_overlap` (parallelism safety).

Authority pattern: **singleton registry, ambient authority for handlers**. A tool's `handler` is a Python callable that closes over whatever the importing module had access to (FS, network, env vars). Tool selection = string name → callable. Schema → LLM, name → dispatch.

## Goblins signature

Each tool becomes a `^tool-cap` actor; the registry is replaced by Mandy's **nonce-registry** (Pattern B from parent SKILL) that mounts caps behind `/object/<base32-id>` URLs. The LLM sees the URL handle, not the cap; the registry vat resolves URL → cap on invocation.

```scheme
;; Nonce registry — Mandy Pattern B
(define-values (registry locator) (spawn-nonce-registry-and-locator))

;; Each tool: a cap with explicit-authority closure
(define (^bash-tool bcom #:fs-cap fs #:net-cap net #:approval-cap appr)
  (methods
    ((invoke args)
     (define cmd (parse args))
     (when (dangerous? cmd)
       (<- appr 'request cmd))
     (<- fs 'exec cmd))))      ; only the caps it was constructed with

(define handle (mount registry (spawn ^bash-tool #:fs-cap fs ...)))
;; → handle is a base32 URL like "/object/abc...xyz"
```

LLM tool list = `[(name, schema, url-handle), …]`. Invocation translator (Mandy Pattern C, `activity->message`) takes `{"tool": name, "args": …}` and rewrites to `(<- (locator handle) 'invoke args)`.

## Translation table

| Hermes call | Goblins message | Notes |
|---|---|---|
| `registry.register(ToolEntry(…))` | mount cap in nonce registry | URL handle minted |
| `registry.dispatch(name, args)` | `(<- (locator handle) 'invoke args)` | LLM sees URL, not cap |
| handler closes over module imports | tool actor takes explicit `#:fs-cap`, `#:net-cap`, etc. | no ambient authority |
| `_execute_tool_calls_concurrent` | parallel `<-` sends; promises join | vat handles concurrency |
| `_paths_overlap` parallelism gate | per-cap exclusion via revocable forwarders | not a global lock |
| `requires_env` declarative dep | constructor parameter (cap or value) | typechecked at spawn |
| `check_fn` (e.g. opt-in toolset) | gate cap construction; absent cap = absent tool | binary, not runtime check |
| MCP dynamic refresh | mount/unmount in registry | atomic; no `_lock` needed |

## Failure modes (closed by this bridge)

- **Tool handler with ambient FS/net authority** — handlers receive caps explicitly; no module-level `import os`.
- **String-name confusion attacks** (e.g. `bash` vs `bash ` vs `BASH`) — there is no name dispatch; URL handle is unforgeable.
- **MCP refresh race with concurrent dispatch** — registry vat serializes mount/unmount; readers see consistent state.
- **Two tools sharing a path through global state** — caps are isolated; sharing requires explicit cap-passing.
- **LLM crafting tool-call to a tool not advertised** — no URL handle in scope = `(locator unknown)` returns `'no-such-cap`.

## Failure modes (introduced; must mitigate)

- **URL handle leaks into memory backend / context** — handles are per-session; rotate on session-end (Mandy registry has built-in TTL).
- **Cap constructor explosion** — large tools with many cap deps. → use a `^cap-bundle` builder per skill (see `hermes-skill-as-cap-module`, row 3).

## Test vector

```python
fs = fs_cap(root='/tmp/sandbox')
net = net_cap(allowlist=['api.openai.com'])
bash = mount(spawn(BashTool, fs_cap=fs, net_cap=net))   # → "/object/abc..."

# LLM gets handle, not cap:
llm_view = {'name': 'bash', 'schema': {...}, 'handle': '/object/abc...'}

# Invocation:
invoke('/object/abc...', {'cmd': 'ls /tmp/sandbox'})    # OK
invoke('/object/abc...', {'cmd': 'ls /etc'})            # CapError (fs scope)
invoke('/object/zzz...', {'cmd': 'ls'})                  # CapError (no-such-cap)

# Concurrent dispatch:
parallel([invoke(h1, args1), invoke(h2, args2)])        # vat handles
# vs Hermes _paths_overlap which needs _lock + manual gating

# MCP refresh during dispatch:
refresh_mcp_tools()      # may mount new caps mid-dispatch
# in-flight calls unaffected; new calls see updated registry
```

## Capability diff

| Property | Hermes (status quo) | Goblins (this bridge) |
|---|---|---|
| Tool selection | string name → callable | URL handle → cap |
| Authority | ambient (handler imports) | explicit (constructor caps) |
| Refresh atomicity | RLock + mutation | mount/unmount in vat |
| Parallelism safety | `_paths_overlap` ad-hoc | per-cap revocable forwarder |
| LLM-cap visibility | handler is a Python callable | only opaque URL handle |
| Failure mode | name-confusion / ambient-leak | no cap = no call |

## Test-harness location

`~/i/goblins-adapter/tests/tool-cap-bisim.scm` (todo). Adversarial probe: prompt-injection asking the LLM to "call the tool whose schema is X but path traversal Y" — Hermes may comply via a related tool; Goblins version cannot construct a path that resolves to a cap not in scope.

## Status: stub

Phase 3 priority. Foundational for `hermes-delegate-as-spawn` (row 2), `hermes-skill-as-cap-module` (row 3), and `hermes-bg-as-vat` (row 4) — all build on the tool-as-cap primitive plus the nonce registry.
