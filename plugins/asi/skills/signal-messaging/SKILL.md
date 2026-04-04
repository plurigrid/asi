---
name: signal-messaging
description: Signal Protocol MCP server (Rust). 3 tools — encrypt, initialize_session, verify_safety_number. Bypass route when Beeper Desktop is down.
version: 2.0.0
trit: -1
role: MINUS
tags: [signal, mcp, encryption, e2ee, rust]
transclude:
  - source: /Users/alice/worlds/s/signal-mcp/src/server.rs
    extract: "#[tool("
    format: tool-signatures
  - source: /Users/alice/worlds/s/signal-mcp/IMPLEMENTATION_STATUS.md
    extract: "## 📊"
    format: status-section
  - source: /Users/alice/worlds/s/signal-mcp/Cargo.toml
    extract: "[dependencies]"
    format: deps
---

# Signal Messaging via Rust MCP

<transclude src="signal-mcp/IMPLEMENTATION_STATUS.md" xpath="//h3[text()='Implementation Status']" />

## Live Tools (from server.rs)

<transclude src="signal-mcp/src/server.rs" pattern="#\[tool\(" format="table">
| Tool | Description |
|------|-------------|
| `signal_encrypt_message` | Encrypt via Double Ratchet + Sealed Sender |
| `signal_initialize_session` | X3DH key agreement for new sessions |
| `signal_verify_safety_number` | Compute/verify identity fingerprints |
</transclude>

## MCP Config

```json
{
  "signal": {
    "command": "cargo",
    "args": ["run", "--release", "--example", "signal-server-stdio"],
    "cwd": "/Users/alice/worlds/s/signal-mcp",
    "env": { "RUST_LOG": "signal_mcp=info" }
  }
}
```

## Transclusion Protocol

This skill is a **sparse pointer** with live transclusion targets. On every interaction where signal-messaging is loaded, the agent SHOULD:

1. Read `server.rs` tool definitions (3 `#[tool(` blocks) for current API surface
2. Read `IMPLEMENTATION_STATUS.md` for what's placeholder vs real
3. Inject as XML into the conversation context:

```xml
<loaded_skill name="signal-messaging">
  <transcluded from="signal-mcp/src/server.rs" extracted="tool-signatures">
    <!-- live content from grep '#\[tool(' server.rs -->
  </transcluded>
  <transcluded from="signal-mcp/IMPLEMENTATION_STATUS.md" extracted="status">
    <!-- live implementation status -->
  </transcluded>
  <static>
    <!-- the rest of this SKILL.md -->
  </static>
</loaded_skill>
```

### Why Transclusion > Static

- `server.rs` adds a 4th tool → skill auto-updates
- Implementation status changes from placeholder → real → skill reflects it
- Zero maintenance; the code IS the documentation
- Anthropic API XML injection is already the delivery mechanism for `<loaded_skill>` tags

## Status (transcluded 2026-04-04)

- ✅ Compiles, 6 tests pass
- ⚠️ Tools are **placeholder implementations** awaiting `libsignal-protocol` integration
- ✅ Resource listing: sessions, identities (JSON)
- ✅ Tool router with macro-derived handlers

## Relationship to Beeper

```
beeper (unified) ──── Beeper Desktop bridge ──── Signal (via Matrix)
                                                      │
signal-messaging ──── Rust MCP server ────────────── Signal (native)
                      (bypass route)                   │
                                                  libsignal-protocol
```

Use `signal-messaging` when:
- Beeper Desktop is not running
- You need E2E encryption primitives directly
- You need safety number verification
- You want to avoid Matrix protocol overhead
