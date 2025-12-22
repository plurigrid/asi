# ruler

Unified AI agent configuration propagation (intellectronica/ruler).

## Core Concept

Centralize rules in `.ruler/` → distribute to 18+ coding agents.

```
.ruler/
├── *.md           # Rules (concatenated alphabetically)
├── ruler.toml     # Agent config + MCP settings
└── mcp.json       # Shared MCP servers
```

## Commands

```bash
ruler init         # Create .ruler/ directory
ruler apply        # Propagate to all agents
ruler revert       # Restore from backups
ruler apply --agents claude,codex,amp
```

## Agent Output Paths

| Agent | Instructions | MCP Config |
|-------|--------------|------------|
| **Claude** | `CLAUDE.md` | `.mcp.json` |
| **Codex** | `AGENTS.md` | `.codex/config.toml` |
| **Amp** | `AGENT.md` | - |
| **Cursor** | `.cursor/rules/*.mdc` | `.cursor/mcp.json` |
| **Copilot** | `.github/copilot-instructions.md` | `.vscode/mcp.json` |
| **Windsurf** | `.windsurf/rules/*.md` | `~/.codeium/windsurf/mcp_config.json` |
| **Aider** | `ruler_aider_instructions.md` | `.mcp.json` |
| **OpenCode** | `AGENTS.md` | `opencode.json` |
| **Gemini** | `GEMINI.md` | `.gemini/settings.json` |

## ruler.toml

```toml
default_agents = ["claude", "codex", "amp", "cursor"]

[gitignore]
enabled = true

[mcp]
enabled = true
strategy = "merge"  # or "overwrite"

[agents.claude]
enabled = true
output_path = "CLAUDE.md"

[agents.codex]
enabled = true
output_path = "AGENTS.md"

[mcp_servers.gay]
command = "julia"
args = ["--project=@gay", "-e", "using Gay; Gay.serve_mcp()"]
env = { GAY_SEED = "1069" }
```

## mcp.json

```json
{
  "mcpServers": {
    "gay": {
      "command": "julia",
      "args": ["--project=@gay", "-e", "using Gay; Gay.serve_mcp()"]
    },
    "firecrawl": {
      "command": "npx",
      "args": ["-y", "firecrawl-mcp"]
    }
  }
}
```

## Workflow

```bash
# 1. Initialize
ruler init

# 2. Add rules
echo "# My Rules" > .ruler/01-basics.md
echo "Use TypeScript" >> .ruler/01-basics.md

# 3. Configure MCP
cat > .ruler/mcp.json << 'EOF'
{"mcpServers": {"gay": {"command": "julia", "args": [...]}}}
EOF

# 4. Apply to all agents
ruler apply

# 5. Revert if needed
ruler revert --keep-backups
```

## GF(3) Integration

```toml
# .ruler/ruler.toml
[bisimulation]
enabled = true
polarity_rotation = true

[bisimulation.agents]
claude = "PLUS"      # +1
codex = "ERGODIC"    # 0
cursor = "MINUS"     # -1
# Sum = 0 mod 3 ✓
```

## Iterative Refinement

1. `ruler apply` → test with agent
2. Edit `.ruler/*.md` rules
3. `ruler apply` → re-test
4. Repeat until stable
5. `git commit .ruler/`

## References

- https://github.com/intellectronica/ruler
- https://deepwiki.com/intellectronica/ruler
