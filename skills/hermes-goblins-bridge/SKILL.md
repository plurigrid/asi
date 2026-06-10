---
name: hermes-goblins-bridge
description: 'Interface-compatible bridges from Hermes Agent harness (~/i/hermes-agent) to Spritely Goblins/OCapN via ~/i/goblins-adapter. Each Hermes capability mapped to a Goblins primitive with a tracked bridge skill, status, and GF(3) polarity. Goal: full feature equivalence under capability discipline.'
gf3_invariant: sum_polarities ≡ 0 (mod 3)
type: bridge-index
---

# Hermes ↔ Goblins Bridge Rubric

Source: `/Users/bob/i/hermes-agent` (NousResearch/hermes-agent, 50MB, 958 .py)
Target: `/Users/bob/i/goblins-adapter` (Guile, 9 files, ~3660 LOC, full OCapN)
Interface contract: each bridge skill exposes a Hermes-shaped Python entrypoint that translates calls into OCapN messages over the goblins-adapter Unix socket / CapTP netlayer.

## Polarity legend (GF(3))

- **+1 play** — agent extends its own action surface
- **0 witness** — agent observes / persists / introspects state
- **−1 coplay** — environment grants/revokes authority

## Tracking table

Protocol fit column: **R** = OCapN/CapTP RPC-shaped · **D** = Syndicate dataspace-shaped · **R+D** = dual

| # | Hermes capability | file:line | Goblins primitive | Bridge skill | Proto | Status | GF(3) |
|---|---|---|---|---|---|---|---|
| 1 | Tool registry / dispatch | `tools/registry.py:99,291` | vat-with-methods · `($ obj 'method args)` | `hermes-tool-as-cap` | R | ✗ todo | +1 |
| 2 | Subagent delegation | `tools/delegate_tool.py` | `spawn` + `<-np` eventual send | `hermes-delegate-as-spawn` | R | ✗ todo | +1 |
| 3 | Skill hub / install | `tools/skills_hub.py` | Syndicate facts (skills as published assertions) | `hermes-skill-as-cap-module` | D | ✗ todo | +1 |
| 4 | Background review | `run_agent.py:2447` | `spawn` (fiber, isolated vat) | `hermes-bg-as-vat` | R | ✗ todo | +1 |
| 5 | Streaming / interrupt | `run_agent.py:5493` | promise + cancel-on-revoke | `hermes-stream-as-promise` | R | ✗ todo | +1 |
| 6 | RL env (Atropos) | `rl_cli.py`, `tinker-atropos/` | environment-as-vat | `hermes-rl-env-as-vat` | R | ✗ todo | +1 |
| 7 | Credential pool | `agent/credential_pool.py` | SturdyRef + revocable forwarder | `hermes-cred-as-sturdy` | R | ✗ todo | 0 |
| 8 | MCP OAuth | `tools/mcp_oauth*.py` | sealer/unsealer + count-limited cap | `hermes-mcp-as-sealed` | R | ✗ todo | 0 |
| 9 | Memory providers | `plugins/memory/{honcho,mem0,...}` | Syndicate dataspace (subscribers react to memory facts) | `hermes-mem-as-dataspace` | D | ✗ todo | 0 |
| 10 | Session persistence | `run_agent.py:2566,2847` | Syndicate event-log dataspace + vat checkpoint | `hermes-session-as-snapshot` | D | ✗ todo | 0 |
| 11 | Context engine | `agent/context_engine.py:31` | Syndicate observers on context dataspace | `hermes-ctx-engine-shim` | D | ✗ todo | 0 |
| 12 | Cron / scheduled | `cron/*` | scheduled facts in dataspace | `hermes-cron-as-dataspace` | D | ✗ todo | 0 |
| 13 | ACP transport | `acp_adapter/*`, `acp_registry/*` | CapTP + Syrup (RPC) · Syndicate registry (state) | `hermes-acp-over-captp` | R+D | ◐ partial | −1 |
| 14 | Gateway platforms | `gateway/platforms/{telegram,whatsapp,qq}` | OCapN netlayer (RPC) · Syndicate presence (state) | `hermes-gateway-as-netlayer` | R+D | ✗ todo | −1 |
| 15 | Approval gating | `tools/approval.py` | revocable forwarder, time/count-limited | `hermes-approval-as-revocable` | R | ✗ todo | −1 |
| 16 | Path security | `tools/path_security.py` | filesystem-cap (single-dir cap) | `hermes-fs-as-cap` | R | ✗ todo | −1 |
| 17 | URL / website safety | `tools/url_safety.py`, `tools/website_policy.py` | network-cap (host-allowlist) | `hermes-net-as-cap` | R | ✗ todo | −1 |
| 18 | TUI surface | `ui-tui/packages/hermes-ink/*` | Hoot → Wasm browser-resident vat | `hermes-tui-via-hoot` | R | ✗ todo | −1 |
| 19 | Federation surface | (new) | ActivityPub actor (Mandy) — outbox = published dataspace | `hermes-as-ap-actor` | D | ✗ todo | 0 |

**Polarity check:** 6 × (+1) + 7 × (0) + 6 × (−1) = 0 — GF(3) balanced ✓
**Protocol split:** 11 R · 6 D · 2 R+D = 19. State-sharing rows (D) cluster on the witness row (5/7) — confirms the polarity:protocol correspondence: witness ≅ shared knowledge, play+coplay ≅ invocation/grant.

## Bridge contract (uniform across all 18)

Every bridge skill exposes the same Python shape so it drops into Hermes' `tools/registry.py` discovery:

```python
# tools/<bridge_name>.py
from hermes.tools.registry import register

@register(toolset="goblins-bridge", schema=...)
async def call(args: dict) -> dict:
    # 1. translate args to OCapN message (Syrup-encoded)
    # 2. send via goblins-adapter Unix socket (or netlayer)
    # 3. await promise, return Hermes-shaped result
```

The Guile side (`~/i/goblins-adapter/`) exposes the dual:

```scheme
;; goblins-adapter/bridges/<bridge-name>.scm
(define-bridge <bridge-name>
  (lambda (vat msg)
    ;; vat-local capability invocation
    ($ (lookup-cap msg) 'method (msg-args msg))))
```

Wire contract: Syrup-encoded record `(<bridge-name> <args>...)` over `~/i/goblins-adapter/sock/captp.sock`, response = Syrup record `(ok <result>)` or `(err <reason>)`.

## Per-bridge spec stubs

Each row above gets a sibling SKILL.md at `~/i/asi/skills/<bridge-skill-name>/SKILL.md` containing:

1. **Hermes signature** — exact tool schema (params, return type)
2. **Goblins signature** — vat method, expected caps in scope
3. **Translation table** — arg-by-arg mapping
4. **Failure modes** — Hermes errors ↔ Goblins promise breakage
5. **Test vector** — round-trip example via `goblins-adapter/test/`
6. **Capability diff** — what Hermes ambiently has vs. what the bridge requires (the *shrinkage*)

## Phasing (priority order)

**Phase 1 — security floor (−1 coplay first, since they shrink the attack surface)**
- 13 `hermes-acp-over-captp` (already partial; flip Hermes to use it as primary transport)
- 16 `hermes-fs-as-cap` (replace path denylist with a directory-cap parameter)
- 17 `hermes-net-as-cap` (replace URL allowlist with a host-cap)
- 15 `hermes-approval-as-revocable` (one-shot caps instead of per-call prompts)

**Phase 2 — state (0 witness)**
- 7 `hermes-cred-as-sturdy` (LLM stops seeing raw keys)
- 8 `hermes-mcp-as-sealed` (MCP token sealed)
- 9 `hermes-mem-as-vat` (collapse 8 memory backends to one vat)
- 10 `hermes-session-as-snapshot` (deterministic replay)
- 11 `hermes-ctx-engine-shim` (pure compute; trivial)
- 12 `hermes-cron-as-vat`

**Phase 3 — action (+1 play)**
- 1 `hermes-tool-as-cap` (the foundation; all subsequent tools become caps)
- 2 `hermes-delegate-as-spawn` (subagent gets a *cap subset*, not the parent's full authority)
- 4 `hermes-bg-as-vat`
- 5 `hermes-stream-as-promise`
- 6 `hermes-rl-env-as-vat`
- 3 `hermes-skill-as-cap-module` (skills become typed cap modules; install = OCapN handshake)

**Phase 4 — surface (−1 coplay, presentation)**
- 14 `hermes-gateway-as-netlayer` (Telegram/WhatsApp/QQ collapse to one netlayer plugin family)
- 18 `hermes-tui-via-hoot` (browser tab = Hoot vat; remove custom Ink/Yoga fork)

## Equivalence claim

After all 18 bridges land:

- Every Hermes tool call goes through a capability — no string-keyed registry, no ambient authority
- LLM never sees credentials, only forwarders
- Subagents are real vats with caller-curated cap subsets (delegation = cap attenuation)
- All transports are CapTP/OCapN — Telegram/WhatsApp/QQ/ACP/Web all funnel through one wire
- Memory + session = one persistent-vat mechanism (8 backends → 1)
- The whole agent can be checkpointed/replayed deterministically
- Browser deploy = compile vat through Hoot

The Hermes harness becomes a **Goblins program** that happens to call LLMs — equivalent function, capability-secure structure.

## Open questions

- **Async impedance**: Hermes is asyncio + threads; Goblins is fibers via guile-fibers. Bridge needs a Python↔fiber bridge (probably via `goblins-adapter`'s existing socket interface).
- **Streaming over CapTP**: Hermes streams partial deltas; CapTP supports promise pipelining but not partial-result streaming natively. May need a stream-vat per response.
- **Skill discovery**: Hermes scans markdown frontmatter; Goblins libs are typed. Need a frontmatter→cap-module compiler step.
- **MCP server compat**: many existing MCP servers are HTTP-only. Bridge `hermes-mcp-as-sealed` may need to keep raw HTTP for those, only sealing the token.

## Mandy patterns (Spritely blog, Jessica Tallon, 2026-01-06)

The Mandy ActivityPub-on-Goblins prototype gives concrete code shapes for several bridges:

### Pattern A — HTTP→vat bridge via `syscaller-free-fiber` + channel

```scheme
;; Reusable for: hermes-acp-over-captp (inbound),
;;               hermes-mcp-as-sealed (legacy MCP HTTP servers),
;;               hermes-as-ap-actor (inbox endpoint).
(define (^web-server bcom router)
  (define (handler req body)
    (define ch (make-channel))
    (with-vat vat
      (on (<- router req body)
          (lambda (resp)
            (syscaller-free-fiber (lambda () (put-message ch (vector 'ok resp)))))
          #:catch
          (lambda (err)
            (syscaller-free-fiber (lambda () (put-message ch (vector 'err err)))))))
    (match (get-message ch) ...))
  (syscaller-free-fiber
   (lambda () (run-server handler 'fibers ...))))
```

The `syscaller-free-fiber` is the key — it spawns a fiber *outside* the vat so suspending it doesn't stall the vat's queue. Direct fix for the **Python-asyncio↔guile-fibers** open question listed above.

### Pattern B — Nonce registry + URL mount

```scheme
(define-values (registry locator)
  (call-with-vat vat spawn-nonce-registry-and-locator))

;; /object/<base32-id> → cap lookup
[("" "object" id)
 (let ((object (<- registry 'fetch (base32-decode id))))
   (<- object 'request))]
```

Use for `hermes-tool-as-cap` — every Hermes tool gets registered with a nonce ID; URL-addressable caps with built-in salting/hashing/persistence. Solves the LLM-never-sees-raw-cap requirement (LLM sees the URL; the registry holds the cap).

### Pattern C — Activity → message translation

```scheme
(define* (activity->message activity #:key send-to)
  (list (or send-to ($ activity 'object))
        ($ activity 'to-method)
        #:object ($ activity 'object)
        #:actor ($ activity 'actor)
        #:target ($ activity 'target)
        #:self activity))
```

Direct template for `hermes-tool-as-cap`'s tool-call → vat-method translator. Hermes tool call `{"name": "Read", "args": {"path": "..."}}` becomes `(<- fs-cap 'read #:path "...")`. The `extend-methods` + `parent` hierarchy maps cleanly onto Hermes toolset hierarchies (`tools/registry.py:75 ToolEntry`).

### Pattern D — Persistent collection via `bcom` + `gset`

```scheme
((add #:key object #:allow-other-keys)
 (bcom (^as2:collection bcom parent (gset-add items object))))
```

Template for `hermes-mem-as-vat` — replaces all 8 memory backends with one `^memory-collection` that uses Goblins persistence (which already supports vat-snapshot/restore). The `#:allow-other-keys` pattern is exactly what's needed when bridging Hermes' loose dict args.

## Mandy → Hermes specifics for row 19 (`hermes-as-ap-actor`)

Each Hermes session = one ActivityPub actor:

- **`/inbox`** ← incoming user messages, federated agent calls (POST `Create`/`Question` activities)
- **`/outbox`** → posted assistant responses, tool results (GET = trajectory)
- **`/object/<id>`** → individual messages, tool-call results, skill artifacts addressable as AS2 objects
- **Profile** → agent metadata: model, available toolsets, declared capabilities

Federation gives:
- multi-agent coordination over an open W3C protocol (no bespoke ACP)
- Hermes ↔ Mastodon/PeerTube/Lemmy interop (an LLM that *follows* you)
- audit trail = outbox (cap-secure since each post is signed by the actor's key)
- `hermes-gateway-as-netlayer` (row 14) collapses further: Telegram/WhatsApp/QQ/Mastodon all become AP-bridged

Source: <https://spritely.institute/news/mandy-activitypub-on-goblins.html> · prototype repo linked from post · FOSDEM 2026 talk by Tallon + Lemmer-Webber.

## Cross-implementation bisimulation

Three reference implementations triangulate the rubric — same OCapN+Syndicate semantics, three host languages:

| Impl | Repo / location | Vat substrate | Status |
|---|---|---|---|
| Guile-Goblins | `/Users/bob/i/goblins-adapter/` | guile-fibers, syrup, full OCapN | reference |
| Python-Hermes | `/Users/bob/i/hermes-agent/` | asyncio + this rubric's bridges | target |
| Troupe-Haskell | NLnet/NGI proposal (Bortolussi et al.) | Troupe (post-Cloud-Haskell) + OCapN + Syndicate add-on | upcoming |

A bridge passes the rubric iff it is observationally indistinguishable from the Goblins reference under the G7 bisimulation oracle (`~/i/agentic-protocols-research/`). Troupe-Haskell becomes the third bisim peer once their OCapN/Syndicate packages land — gives a typed, GHC-checked corner of the equivalence triangle.

## Syndicate ↔ OCapN unification

The Troupe proposal explicitly bundles **Syndicate** (state-sharing dataspace) with **OCapN** (RPC + caps), treating them as duals. The Proto column (R/D/R+D) in the tracking table makes this concrete:

- **R rows (RPC-shaped, 11)**: invocation, delegation, revocation, streaming — naturally OCapN. Polarity skews +1/−1.
- **D rows (dataspace-shaped, 6)**: skill hub, memory, session, context, cron, federation — naturally Syndicate. All sit on the witness row (polarity 0).
- **R+D rows (dual, 2)**: ACP transport and gateway — RPC for the call, dataspace for the registry/presence.

The polarity:protocol correspondence is not coincidence — it falls out of GF(3): witness (0) ≅ shared knowledge, play(+1)+coplay(−1) ≅ invocation/grant.

## Cross-refs

- Goblins adapter: `/Users/bob/i/goblins-adapter/` (memory: 9 Guile files, full OCapN)
- Hermes harness: `/Users/bob/i/hermes-agent/` (just cloned)
- Distributed Systems memory: `zig-syrup ↔ Nashator :9999 ↔ Goblins CapTP`
- Agentic Protocol Research: `~/i/agentic-protocols-research/` (G7 bisimulation oracle, passport.gay canonical form)
- Troupe-Haskell + OCapN + Syndicate proposal: NLnet/NGI funding round (post-Cloud-Haskell actor lib + OCapN net + Syndicate dataspace). See memory `troupe-syndicate-haskell.md`.
