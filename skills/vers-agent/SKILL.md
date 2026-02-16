---
name: vers-agent
description: ACP-compliant AI agent harness with CLI/HTTP interface. Use when running Claude Code or other agents via unified protocol, managing sessions, or debugging agent workflows.
---

# vers-agent

ACP (Agent Client Protocol) harness for AI coding agents with session persistence and streaming.

## Quick Start

```bash
bun install && bun run build
export ANTHROPIC_API_KEY=sk-ant-...
./vers-agent
```

## Essential Commands (justfile)

| Action | Command |
|--------|---------|
| **Start everything** | `just up` |
| **Server only** | `just server` |
| **CLI only** | `just cli` |
| **Status dashboard** | `just status` |
| **Pre-commit check** | `just check` |
| **Nuclear reset** | `just nuke` |
| **One-shot prompt** | `just ask "your prompt"` |

## Modes

| Flag | Description |
|------|-------------|
| `./vers-agent` | Server + CLI (default) |
| `--server` | HTTP server only (:9999) |
| `--cli` | CLI connecting to localhost |
| `--url <host>` | CLI connecting to remote |
| `--local` | Local mode with debug logging |

## CLI Keybindings

- `Enter` - Submit | `Shift+Enter` - Newline
- `Tab` - Autocomplete | `Ctrl+C` - Cancel/Exit
- `@path` - File completion | `/cmd` - Commands

## Session Commands

- `/new` - New session | `/continue` - Resume last
- `/sessions` - List all | `/model` - Change model
- `/agent` - Switch agent | `/plan` - Toggle plan mode

## Troubleshooting

| Problem | Fix |
|---------|-----|
| Port in use | `just kill-port` |
| Auth locked | `just reset-claim` |
| Full reset | `just nuke` |
| Complete wipe | `just pristine` |

## API Endpoints

- `POST /rpc` - JSON-RPC handler
- `GET /events` - SSE stream
- `GET /health` - Health check
- `GET /metrics` - Prometheus metrics

## Data Location

`~/.vers-agent/` contains sessions.db, tokens.json, config.json, and logs.
