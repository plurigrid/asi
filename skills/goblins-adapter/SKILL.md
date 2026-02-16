---
name: openclaw-goblins-adapter
description: ElizaOS/OpenClaw → Goblins OCapN adapter (study + bridge)
version: 0.1.0
metadata:
  trit: 0
  study: elizaOS/openclaw-adapter
---

# OpenClaw → Goblins Adapter

## Study: elizaOS/openclaw-adapter

The `openclaw-adapter` bridges ElizaOS plugins into OpenClaw via:

| File | ElizaOS → OpenClaw |
|---|---|
| `action-to-tool.ts` | Action → Tool (params: JSON Schema → TypeBox) |
| `provider-to-hook.ts` | Provider → `before_agent_start` hook |
| `service-adapter.ts` | Service → Service (eager start) |
| `evaluator-to-hook.ts` | Evaluator → lifecycle hooks |
| `runtime-bridge.ts` | IAgentRuntime → RuntimeBridge shim |
| `in-memory-store.ts` | IDatabaseAdapter → LRU InMemoryStore (10K cap) |
| `schema-converter.ts` | JSON Schema → TypeBox + known wallet schemas |

**Critical pattern**: RuntimeBridge is a _shim_, not a full runtime embed.

## This Adapter: ElizaOS → Goblins OCapN

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
| /eliza route | Bootstrap object (pos 0) | Single entry point |
| Tool schema | Syrup record | ^schema-bridge |

## Security Model Upgrade

```
MCP/ElizaOS: ambient authority
  token → role → permissions → action
  (confused deputy attacks possible)

Goblins/OCapN: structural authority
  ref = authority (POLA)
  (confused deputy impossible by construction)
```

## Files

| File | LOC | Role |
|---|---|---|
| `goblins-adapter.scm` | ~350 | Core adapter (9 actor types) |
| `MAPPING.md` | ~200 | Detailed concept mapping |
| `SKILL.md` | this | Skill definition |

## GF(3)

```
Actions  = +1 (generative — create capabilities)
Providers = -1 (constraining — read-only attenuation)
Services = 0  (ergodic — background transport)
```

Adapter enforcer: registration sum ≡ 0 (mod 3).

## Usage

```scheme
(define-values (vat bridge schema session gf3)
  (spawn-goblins-adapter "my-agent" settings))

;; Register ElizaOS-shaped plugin
($ bridge register-plugin plugin-spec)

;; Invoke tool (CapTP bootstrap)
($ bridge invoke "tool-name" params)

;; Bridge MCP call → CapTP deliver
($ session mcp-call->deliver sid "tool" params)
```

## Triads

```
captp (0) ⊗ openclaw-goblins-adapter (0) ⊗ gay-mcp (+1) → needs -1
shadow-goblin (-1) ⊗ this (0) ⊗ agent-o-rama (+1) = 0 ✓
keychain-secure (-1) ⊗ this (0) ⊗ pulse-mcp-stream (+1) = 0 ✓
```
