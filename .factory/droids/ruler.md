---
name: ruler
description: Unified AI agent configuration propagation across 18+ coding assistants.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ruler

Unified AI agent configuration propagation across 18+ coding assistants.

**Repository**: https://github.com/intellectronica/ruler
**Documentation**: https://deepwiki.com/intellectronica/ruler

---

## Overview

Ruler centralizes AI agent instructions in `.ruler/` and distributes them to all configured agents via `ruler apply`. Supports Model Context Protocol (MCP) propagation with merge/overwrite strategies.

```
.ruler/
├── *.md           # Rules (concatenated alphabetically)
├── ruler.toml     # Agent config + MCP settings
└── mcp.json       # Shared MCP servers
```

---

## Installation

```bash
npm install -g ruler
# or
npx ruler init
```

---

## Commands

### ruler init

Creates `.ruler/` directory with default files:

```bash
ruler init           # Local project
ruler init --global  # ~/.config/ruler/
```

**Creates:**
- `instructions.md` - Central AI instructions
- `ruler.toml` - Configuration file
- `mcp.json` - MCP server definitions

### ruler apply

Propagates rules to all configured agents:

```bash
ruler apply                          # All default agents
ruler apply --agents claude,codex    # Specific agents
ruler apply --no-mcp                 # Skip MCP propagation
ruler apply --mcp-overwrite          # Replace native MCP configs
ruler apply --no-gitignore           # Skip .gitignore updates
```

### ruler revert

Restores files from backups:

```bash
ruler revert                  # Restore all, delete backups
ruler revert --keep-backups   # Restore but keep .bak files
```

---

## Supported Agents (18)

| Agent | Identifier | Instructions Output | MCP Config |
|-------|------------|---------------------|------------|
| **GitHub Copilot** | `copilot` | `.github/copilot-instructions.md` | `.vscode/mcp.json` |
| **Claude Code** | `claude` | `CLAUDE.md` | `.mcp.json` |
| **OpenAI Codex CLI** | `codex` | `AGENTS.md` | `.codex/config.toml` |
| **Jules** | `jules` | `AGENTS.md` | - |
| **Cursor** | `cursor` | `.cursor/rules/ruler_cursor_instruct