# OpenClaw ↔ ElizaOS ↔ Goblins: Concept Mapping

## Three-Way Translation Table

| # | ElizaOS | OpenClaw | Goblins/OCapN |
|---|---------|----------|---------------|
| 1 | Action | Tool | ^action-actor ($method) |
| 2 | Action.validate() | Tool pre-check | Guard actor pre-fn |
| 3 | Action.handler() | Tool.execute() | $ actor execute msg |
| 4 | Action.similes[] | Tool aliases | (methods [alias ...]) |
| 5 | Provider | before_agent_start hook | ^provider-cap (read-only ref) |
| 6 | Service | Service (eager) | ^service-actor in dedicated vat |
| 7 | Evaluator (pre) | message hook | ^guard-actor pre-fn |
| 8 | Evaluator (post) | agent-end hook | ^guard-actor post-fn |
| 9 | IAgentRuntime | Gateway + PiEmbeddedRunner | ^vat-bridge (actor shim) |
| 10 | IDatabaseAdapter | SQLite + FTS5 | Actor state (bcom) + cells |
| 11 | Memory (vector) | ~/.openclaw/memory/*.sqlite | ($ bridge store-memory) |
| 12 | Plugin | Extension (channel/tool/memory/provider) | Vat-spawned actor set |
| 13 | Plugin.init() | Extension activation | (register-plugin) init phase |
| 14 | Route | HTTP route (/eliza prefix) | Bootstrap object method |
| 15 | Config | openclaw.json | Settings alist → get-setting |
| 16 | Session | Session (append-only events) | CapTP session (Ed25519) |
| 17 | JSON Schema | TypeBox schema | Syrup record descriptor |
| 18 | Event | Hook trigger | <- (async send) |
| 19 | Room | Channel thread | Vat (shared actor container) |
| 20 | Participant | Allowed sender | Capability holder |

## Message Flow Comparison

### ElizaOS → OpenClaw (via openclaw-adapter)

```
Platform msg → Channel Adapter → Gateway WS → PiEmbeddedRunner
  → Context (AGENTS.md + SOUL.md + TOOLS.md + Skills)
  → LLM call → Tool execution → Response
```

### ElizaOS → Goblins (via goblins-adapter)

```
Platform msg → Channel → ^captp-session-bridge (token→session)
  → ^vat-bridge (context assembly from ^provider-caps)
  → $ bridge invoke "tool" params
    → ^guard-actor pre-fn (evaluator)
      → ^action-actor execute msg (action handler)
    → ^guard-actor post-fn (evaluator)
  → ^captp-session-bridge (deliver-result→mcp)
  → Response
```

### Direct CapTP Flow (native Goblins)

```
Remote peer → op:start-session (Ed25519 exchange)
  → op:deliver to bootstrap (pos 0) → "invoke" "tool" params
  → Promise pipelining (no round-trip for chained calls)
  → op:deliver result → Remote peer
```

## Wire Format Comparison

### MCP (JSON-RPC)
```json
{"jsonrpc":"2.0","method":"tools/call",
 "params":{"name":"send_tokens","arguments":{"to":"0x...","amount":"1.5"}},
 "id":1}
```

### Syrup (OCapN)
```
<10'trit-event 1- 1069+ 7"world-a 1707836400+>
```

### Conversion (^schema-bridge)
```scheme
;; JSON Schema → Syrup descriptor
($ schema json-schema->syrup-desc
   '((type . "object")
     (properties . ((to . ((type . "string")))
                    (amount . ((type . "number")))))))
;; → ((to (type . string) (required . #f))
;;    (amount (type . float) (required . #f)))
```

## Security Model Comparison

| Property | MCP | OpenClaw | Goblins |
|----------|-----|----------|---------|
| Auth | OAuth 2.1 | Allowlist + tokens | Capability refs |
| Delegation | Token forwarding | Config inheritance | Cap attenuation |
| Revocation | Token expiry | Config update | Cap revoke / GC |
| Confused deputy | Possible | Possible | Impossible |
| Ambient authority | Yes | Yes | No |
| POLA | Manual | Manual | Structural |

## Zig Transport Layer (existing)

The adapter uses existing zig-syrup for wire transport:

| File | Role | LOC |
|------|------|-----|
| `zig-syrup/src/syrup.zig` | Syrup serialization | ~500 |
| `zig-syrup/src/message_frame.zig` | Length-prefix framing | 232 |
| `zig-syrup/src/tcp_transport.zig` | TCP netlayer | 205 |
| `zig-syrup/src/goblins_ffi.zig` | C ABI for Guile | 320 |

### Adapter Files (this repo)

| File | Role | LOC |
|------|------|-----|
| `goblins-adapter.scm` | Core adapter (^vat-bridge, ^action-actor, etc.) | ~500 |
| `rosette-actor.scm` | Phyllotaxis actors (^primordium, ^meristem, ^garden) | ~390 |
| `propagator-nash.scm` | SDF Ch7 propagator Nash solver | ~420 |
| `rosette-captp-bridge.scm` | TCP CapTP bridge to Nashator | ~555 |
| `concurrent-nash.scm` | Temperature racing + adaptive scheduler | ~390 |
| `hoot-websocket.scm` | Hoot/WASM WebSocket netlayer | ~556 |
| `brassica-crdt.scm` | CRDT actors (LWW, OR-Set, PN-Counter, MV-Reg) | ~541 |
| `sturdy-refs.scm` | Persistent capability refs + gift table | ~415 |
| `handoff.scm` | Third-party introduction + tool marketplace | ~395 |

## Implementation Status

| # | Feature | File | Status |
|---|---------|------|--------|
| 1 | TCP bridge | `rosette-captp-bridge.scm` | ✅ Done |
| 2 | Hoot/WASM | `hoot-websocket.scm` | ✅ Done |
| 3 | Brassica CRDT | `brassica-crdt.scm` | ✅ Done |
| 4 | Sturdy refs | `sturdy-refs.scm` | ✅ Done |
| 5 | Third-party handoff | `handoff.scm` | ✅ Done |

## MAC Address Forensics via CapTP (NEW 2026-02-13)

The MAC→Color pipeline threads through Goblins as capability-secured device identity:

```
MAC 50:BB:B5:4D:BD:04 → Gay.jl seed 88767130877188
  → ^mac-forensics-actor (owns device color identity)
    → solve-remote! to Nashator :9999 (device_classification game)
    → CapTP capability ref to device color (#DD794F)
    → ^sturdy-ref for persistent device identity (survives restarts)
    → ^attenuated-actor for read-only color queries
```

**OUI forensics as capability model**:
- Device color = capability reference (share, attenuate, revoke)
- OUI class = manufacturer capability domain
- ARP spoofing detection = color identity mismatch via Galois closure
- Network topology = colored graph with GF(3) conservation law

**Wire path**: Gay MCP → Nashator RPC → zig-syrup frame → rosette-captp-bridge → actor

## What's Next

1. **basin-hedges oracle-remote**: TCP PayoffOracle impl over zig-syrup wire (~150 LOC)
2. **Gay MCP ↔ Nashator bridge**: Seed from MCP, game solve via RPC, return colored result
3. **Hoot compilation**: `guild compile-wasm hoot-websocket.scm` (needs Hoot toolchain)
4. **Browser demo**: HTML + JS loading the .wasm, connecting to Nashator WS
5. **Peer discovery**: mDNS/NATS-based peer advertisement for auto-connect
6. **Audit trail**: CRDT-backed immutable log of all introductions + revocations
7. **Brassica persistence**: SQLite-backed CRDT state for crash recovery
8. **HEVM oracle**: Connect ^hevm-oracle-actor to real HEVM binary for on-chain verification
