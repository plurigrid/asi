# @topos/localsend-mcp

LocalSend P2P file transfer MCP server with Tailscale/NATS discovery and Gay.jl deterministic colors.

## Installation

```bash
npx -y @topos/localsend-mcp
```

## Configuration

### Amp (`~/.config/amp/settings.json`)

```json
{
  "mcpServers": {
    "localsend": {
      "command": "npx",
      "args": ["-y", "@topos/localsend-mcp"]
    }
  }
}
```

### Claude Desktop (`~/.claude/claude_desktop_config.json`)

```json
{
  "mcpServers": {
    "localsend": {
      "command": "npx",
      "args": ["-y", "@topos/localsend-mcp"]
    }
  }
}
```

### VS Code (`.vscode/settings.json` or user settings)

```json
{
  "mcp.servers": {
    "localsend": {
      "command": "npx",
      "args": ["-y", "@topos/localsend-mcp"]
    }
  }
}
```

### OpenCode (`~/.config/opencode/config.json`)

```json
{
  "mcpServers": {
    "localsend": {
      "command": "npx",
      "args": ["-y", "@topos/localsend-mcp"]
    }
  }
}
```

## Tools

| Tool | Description |
|------|-------------|
| `localsend_advertise` | Advertise presence on network |
| `localsend_list_peers` | Discover peers via multicast/Tailscale/NATS |
| `localsend_negotiate` | Establish session with peer |
| `localsend_send` | Send file to peer |
| `localsend_probe` | Measure throughput/RTT |
| `localsend_session_status` | Check session metrics and spectral gap |

## Spectral Gap Tuning

The server uses a spectral gap heuristic for throughput optimization:

```
spectral_gap = 1.0 - (observed_throughput / target_throughput)
```

Stop tuning when `spectral_gap <= 0.25` (>= 75% of target throughput).

## Gay.jl Colors

Each peer gets a deterministic color using SplitMix64 + golden angle:

```typescript
const GAY_SEED = 0x6761795f636f6c6fn; // "gay_colo"
const GOLDEN = 0x9e3779b97f4a7c15n;
```

## Development

```bash
cd packages/localsend-mcp
npm install
npm run build
npm run dev  # Opens MCP Inspector
```

## License

MIT
