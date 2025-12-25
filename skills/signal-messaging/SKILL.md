---
name: signal-messaging
description: Send and receive Signal messages via MCP. Use this skill when you need to interact with Signal messenger - sending messages, reading conversations, or automating Signal-based workflows.
compatibility: Requires signal-mcp server built with Cargo. Signal account must be registered.
geodesic: true
moebius: "μ(n) ≠ 0"
---

# Signal Messaging via MCP

Interact with Signal messenger through the local MCP server.

## Setup

The Signal MCP server is configured in `~/.mcp.json`:

```json
{
  "signal": {
    "command": "cargo",
    "args": ["run", "--release", "--example", "signal-server-stdio"],
    "cwd": "/Users/alice/signal-mcp",
    "env": {
      "RUST_LOG": "signal_mcp=info"
    }
  }
}
```

## Prerequisites

1. Clone and build the signal-mcp server:
   ```bash
   cd /Users/alice/signal-mcp
   cargo build --release --example signal-server-stdio
   ```

2. Register/link your Signal account with the server

## Usage

Use `read_mcp_resource` to interact with Signal:

```json
{"server": "signal", "uri": "signal://..."}
```

## Capabilities

- Send messages to contacts or groups
- Read incoming messages
- List conversations
- Handle attachments

## Troubleshooting

- Ensure the server starts: `cargo run --release --example signal-server-stdio`
- Check logs: `RUST_LOG=signal_mcp=debug`
- Verify Signal account is registered/linked
- Restart Amp after config changes

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
