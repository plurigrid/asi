---
name: hermes-ctx-engine-shim
description: Re-ground Hermes' ContextEngine plugin lifecycle (on_session_start / update_from_response / should_compress / compress / on_session_end) on Syndicate dataspace observers. Token-state becomes published facts; compression is a subscriber that reacts to threshold-crossings; multiple engines coexist by observing the same dataspace.
type: bridge
parent: hermes-goblins-bridge
row: 11
proto: D
polarity: 0
status: stub
---

# hermes-ctx-engine-shim

Phase 2. Lightest of the D rows — this is a re-shaping rather than a re-implementation.

## Hermes signature

`/Users/bob/i/hermes-agent/agent/context_engine.py:31`

```python
class ContextEngine(ABC):
    last_prompt_tokens: int
    last_completion_tokens: int
    last_total_tokens: int
    threshold_tokens: int
    context_length: int

    def on_session_start(self, …): ...
    def update_from_response(self, response): ...
    def should_compress(self) -> bool: ...
    def compress(self, messages) -> List[Message]: ...
    def on_session_end(self): ...
```

Plugins in `plugins/context_engine/<name>/`. One engine active at a time, selected via `context.engine` in config.yaml. Built-in is `ContextCompressor`; third-party drop-in is LCM. `run_agent.py:7423,1981` — compression callsites.

Authority pattern: **plugin-method dispatch**. Engine fields are read directly by `run_agent.py` (tight coupling); engine method calls happen at hard-coded points in the run loop.

## Goblins signature

A `^ctx-dataspace` actor that publishes token-state facts and accepts observers. Engines = observers; multiple can coexist (e.g. compressor for the live model + LCM for retrieval-side parallel engine + telemetry recorder for analytics).

```scheme
(define (^ctx-dataspace bcom)
  (define ds (spawn ^dataspace))
  (methods
    ((session-start sid . opts)
     (assert! ds `(session ,sid #:state active ,@opts)))
    ((response sid usage)
     (assert! ds `(usage ,sid ,(now) ,usage))
     (when (> (cumulative-tokens sid) (threshold))
       (assert! ds `(should-compress ,sid))))
    ((session-end sid)
     (retract! ds `(session ,sid . _))
     (assert! ds `(session ,sid #:state ended)))
    ((subscribe pattern observer)
     (observe ds pattern observer))))

;; Compressor as observer:
(observe ds '(should-compress ?sid)
         (lambda (sid)
           (define new-msgs (compress (session-messages sid)))
           (assert! ds `(compressed ,sid ,new-msgs))
           (retract! ds `(should-compress ,sid))))
```

Run-loop becomes a publisher; engines become subscribers. Multiple engines = multiple subscribers, no plugin-singleton config.

## Translation table

| Hermes call | Goblins message | Notes |
|---|---|---|
| `on_session_start(...)` | `(<- ctx 'session-start sid ...)` | publishes session-active fact |
| `update_from_response(r)` | `(<- ctx 'response sid usage)` | publishes usage; auto-publishes should-compress on threshold |
| `should_compress()` | `(observe ds '(should-compress ?sid))` | subscriber pattern, not a poll |
| `compress(msgs) → msgs'` | observer asserts `(compressed sid msgs')` | publish-back; loop replaces context on observation |
| `on_session_end()` | `(<- ctx 'session-end sid)` | retract active, assert ended |
| swap engine | un-observe old, observe new | live, no restart |
| run multiple engines | multiple observers on same dataspace | first-class concurrency |

## Failure modes (closed by this bridge)

- **Plugin singleton constraint** — multiple engines coexist; each is an observer.
- **Engine field reads from run_agent.py = tight coupling** — facts are public dataspace queries, no direct field access.
- **Engine swap requires restart** — observe/un-observe is dynamic.
- **Compression race** — assertion-then-retraction with vat-message ordering eliminates the "compressed twice in parallel" bug.

## Failure modes (introduced; must mitigate)

- **Subscriber storm on every response** — pattern-match in dataspace, not in subscriber; only `should-compress` facts wake the compressor.
- **Stale observers after session-end** — observe with session-id pattern; auto-uninstall on session-ended fact.

## Test vector

```python
ctx = ctx_dataspace()
compressor = observe(ctx, '(should-compress ?sid)', do_compress)
ctx.session_start('s1', threshold=100_000)
for r in responses:
    ctx.response('s1', r.usage)
# When threshold crossed, do_compress observes the fact and asserts (compressed s1 ...).
# Run loop observes that and swaps the message list.

# Multi-engine:
lcm = observe(ctx, '(should-compress ?sid)', do_lcm_index)
# Both compressor and LCM react to same fact, in parallel, in their own vats.

# Live swap:
un_observe(compressor)
observe(ctx, '(should-compress ?sid)', do_summarize_v2)
# No restart; next threshold-crossing fires v2.
```

## Capability diff

| Property | Hermes (status quo) | Goblins (this bridge) |
|---|---|---|
| Engine count | 1 (config.yaml) | N observers |
| Coupling | engine.field read by run_agent | dataspace pattern-match |
| Swap | restart with new config | live un-observe / observe |
| Compression race | possible if called twice | dataspace ordering |
| Multi-engine | not supported | first-class |

## Test-harness location

`~/i/goblins-adapter/tests/ctx-engine-bisim.scm` (todo). Bisim probe: same response sequence, threshold, expect same compressed messages. Multi-engine probe: assert non-interference (compressor's output not affected by LCM's parallel observation).

## Status: stub

Phase 2 priority. Lightest D row — minimal new code, large architectural simplification (run-loop no longer reads engine fields directly).
