---
name: skill-specification
description: Agent Skills formal specification for cross-platform compatibility. Ensures skills are evolutionarily robust across Claude, Codex, Cursor, Amp, and future agents.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Skill Specification

Formal specification for evolutionarily robust agent skills.

## Why This Matters

Skills that follow the spec work across:
- **Claude Code** (Anthropic)
- **Codex CLI** (OpenAI)
- **Cursor** (Anysphere)
- **Amp** (Sourcegraph)
- **Letta** (memGPT)
- Future agents

Non-compliant skills break silently or fail validation.

## SKILL.md Schema

```yaml
---
name: skill-name              # REQUIRED: lowercase, hyphens, 1-64 chars
description: What and when    # REQUIRED: max 1024 chars, no < or >
license: Apache-2.0           # optional
compatibility: Requires git   # optional, max 500 chars
metadata:                     # optional: custom key-value pairs
  trit: 0
  author: bmorphism
  version: "1.0"
allowed-tools: Bash Read      # optional, experimental
---

# Body content (Markdown)
```

## Field Constraints

| Field | Required | Rules |
|-------|----------|-------|
| `name` | ✓ | `[a-z0-9-]+`, no `--`, no leading/trailing `-`, max 64 |
| `description` | ✓ | 1-1024 chars, no `<` or `>`, includes WHEN to use |
| `license` | ✗ | Short name or file reference |
| `compatibility` | ✗ | Environment requirements, max 500 |
| `metadata` | ✗ | Arbitrary k:v for custom fields |
| `allowed-tools` | ✗ | Space-delimited tool names |

## Evolutionary Robustness Patterns

### 1. Progressive Disclosure

```
Level 1: name + description (~100 tokens) - loaded at startup
Level 2: SKILL.md body (<5000 tokens) - loaded on activation
Level 3: scripts/, references/, assets/ - loaded on demand
```

Keep SKILL.md under 500 lines. Move details to `references/`.

### 2. Cross-Platform Compatibility

```yaml
# BAD - platform-specific
allowed-tools: claude_desktop_mcp

# GOOD - generic capability
compatibility: Requires MCP server access
```

### 3. Self-Validation Hook

Include validation in your skill:

```bash
# scripts/validate.sh
skills-ref validate "$(dirname "$0")/.."
```

### 4. Semantic Versioning in Metadata

```yaml
metadata:
  version: "2.1.0"
  breaking-changes: