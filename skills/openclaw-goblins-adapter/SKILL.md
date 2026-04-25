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

## Concrete Affordance: Local Files, Upstream Repos, and Testing

### Local `goblins-adapter.scm` Implementation

A full working Guile Scheme implementation exists at three locations:

| Path | Description |
|---|---|
| `/Users/alice/v/asi/skills/goblins-adapter/goblins-adapter.scm` | Primary copy (511 lines) |
| `/Users/alice/v/.agents/skills/openclaw-goblins-adapter/goblins-adapter.scm` | Agent-visible copy |
| `/Users/alice/v/worlds/a/asi/skills/goblins-adapter/goblins-adapter.scm` | World-a copy |

The `.scm` file implements all 9 components from the mapping table above:
`^action-actor`, `^provider-cap`, `^service-actor`, `^guard-actor`,
`^vat-bridge`, `^schema-bridge`, `^captp-session-bridge`, `^gf3-adapter-enforcer`,
and the top-level `spawn-goblins-adapter` entry point.

### Upstream Repositories

```bash
# ElizaOS openclaw-adapter (TypeScript, the source material for the mapping)
git clone https://github.com/elizaOS/openclaw-adapter.git

# Guile Goblins (the OCapN actor framework this adapter targets)
git clone https://gitlab.com/spritely/guile-goblins.git

# Goblins documentation / OCapN spec
git clone https://gitlab.com/ocapn/ocapn.git
```

### Install Guile Goblins

```bash
# Via Guix (recommended)
guix install guile guile-goblins

# Or via Flox
flox install guile

# Then install Goblins from source:
cd /tmp && git clone https://gitlab.com/spritely/guile-goblins.git
cd guile-goblins && ./configure && make && make install
```

### Testing the Adapter

```bash
# Load and test the adapter in Guile REPL
guile -L /Users/alice/v/asi/skills/goblins-adapter/ -l goblins-adapter.scm -c '
  (use-modules (goblins))
  (define-values (vat bridge schema session gf3)
    (spawn-goblins-adapter "test-agent"
      (list (cons (quote test-key) "test-val"))))
  (display (with-vat vat ($ bridge describe)))
  (newline)
  (display (with-vat vat ($ gf3 balanced?)))
  (newline)
'
```

### Quick Smoke Test (no Goblins required)

If Guile Goblins is not installed, verify the file parses:

```bash
guile -c '
  (use-modules (ice-9 read))
  (call-with-input-file
    "/Users/alice/v/asi/skills/goblins-adapter/goblins-adapter.scm"
    (lambda (port)
      (let loop ((expr (read port)) (count 0))
        (if (eof-object? expr)
            (format #t "Parsed ~a top-level expressions successfully.~%" count)
            (loop (read port) (+ count 1))))))
'
```

### npm Package (ElizaOS side)

```bash
# The TypeScript openclaw-adapter (if you need the ElizaOS side)
npm install @elizaos/openclaw-adapter
# or from source:
git clone https://github.com/elizaOS/openclaw-adapter.git
cd openclaw-adapter && npm install && npm run build
```


## ACP atlas

Part of: `acp-commons`.
