---
name: openclaw-goblins-adapter
description: Bridge ElizaOS/OpenClaw plugins to Goblins OCapN actors. Maps ambient authority (token/role/ACL) to structural authority (capability references). Triggers: openclaw, elizaos, goblins, ocapn, capability security.
---

# OpenClaw → Goblins Adapter

## ElizaOS → OpenClaw Mapping (from elizaOS/openclaw-adapter)

| File | ElizaOS → OpenClaw |
|---|---|
| `action-to-tool.ts` | Action → Tool (JSON Schema → TypeBox) |
| `provider-to-hook.ts` | Provider → `before_agent_start` hook |
| `service-adapter.ts` | Service → Service (eager start) |
| `evaluator-to-hook.ts` | Evaluator → lifecycle hooks |
| `runtime-bridge.ts` | IAgentRuntime → RuntimeBridge shim |
| `schema-converter.ts` | JSON Schema → TypeBox + wallet schemas |

**Critical**: RuntimeBridge is a shim, not a full runtime embed.

## ElizaOS → Goblins OCapN Mapping

| ElizaOS | Goblins | Why |
|---|---|---|
| Action | ^action-actor | Caps = authority (not ACL) |
| Provider | ^provider-cap | Read-only attenuated ref (POLA) |
| Service | ^service-actor in vat | Isolation via event loop |
| Evaluator | ^guard-actor | Proxy composition |
| IAgentRuntime | ^vat-bridge | Transactional actor state |
| IDatabaseAdapter | Actor state (bcom) | Automatic rollback |
| JSON Schema | Syrup record descriptor | Wire-native |
| OAuth session | CapTP session (Ed25519) | Structural authority |

## Security Model Upgrade

```
MCP/ElizaOS: ambient authority
  token → role → permissions → action (confused deputy possible)

Goblins/OCapN: structural authority
  ref = authority, POLA (confused deputy impossible by construction)
```

## Usage

```scheme
(define-values (vat bridge schema session)
  (spawn-goblins-adapter "my-agent" settings))

($ bridge register-plugin plugin-spec)
($ bridge invoke "tool-name" params)
($ session mcp-call->deliver sid "tool" params)
```
