---
name: deepwiki-mcp
description: DeepWiki MCP for AI-powered GitHub repo documentation. Query any public repo indexed on deepwiki.com. Distilled from usage across Codex, Copilot sessions.
version: 2.0.0
---

# DeepWiki MCP

Query AI-generated documentation for any public GitHub repository via MCP.

## Quick Start

```bash
# Ask a question about any repo
curl -s -X POST "https://mcp.deepwiki.com/mcp" \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{
    "name":"ask_question",
    "arguments":{"repoName":"owner/repo","question":"How does X work?"}
  }}'
```

## Server Configuration

| Protocol | URL | Clients |
|----------|-----|---------|
| Streamable HTTP | `https://mcp.deepwiki.com/mcp` | Amp, Codex, OpenAI |
| SSE | `https://mcp.deepwiki.com/sse` | Claude Desktop, Cursor |

**Amp/Codex (.mcp.json)**:
```json
{"mcpServers":{"deepwiki":{"serverUrl":"https://mcp.deepwiki.com/mcp"}}}
```

**Claude Code**:
```bash
claude mcp add -s user -t http deepwiki https://mcp.deepwiki.com/mcp
```

## Tools

### `ask_question`
```json
{"name":"ask_question","arguments":{"repoName":"owner/repo","question":"..."}}
```

### `read_wiki_structure`
```json
{"name":"read_wiki_structure","arguments":{"repoName":"owner/repo"}}
```

### `read_wiki_contents`
```json
{"name":"read_wiki_contents","arguments":{"repoName":"owner/repo","topic":"Overview"}}
```

## Distilled Usage Patterns

From `.codex/history.jsonl` and `.copilot/session-state/*/events.jsonl`:

### Top Queried Repos

| Repo | Count | Domain |
|------|-------|--------|
| `plurigrid/ontology` | 295 | Architecture |
| `plurigrid/asi` | 216 | ASI Framework |
| `AlgebraicJulia/Catlab.jl` | 30 | Category Theory |
| `AlgebraicJulia/ACSets.jl` | 25 | C-Sets |
| `discopy/discopy` | 20 | Monoidal Cats |
| `redplanetlabs/agent-o-rama` | 18 | Rama Agents |

### Common Patterns

**1. Mission Query** (site content generation):
```bash
ask_question("plurigrid/ontology", "Provide a concise mission statement")
```

**2. Architecture Dive**:
```bash
ask_question("AlgebraicJulia/Catlab.jl", "How do wiring diagrams compose?")
```

**3. Random-Walk Fusion** (pair with skill):
```
1. skill: deepwiki-mcp
2. skill: random-walk-fusion
3. Query 3 repos for cross-domain synthesis
```

## Indexed Repos

| Repo | Status |
|------|--------|
| `AlgebraicJulia/Catlab.jl` | ✅ 16 pages |
| `discopy/discopy` | ✅ 23 pages |
| `redplanetlabs/agent-o-rama` | ✅ 28 pages |
| `plurigrid/ontology` | ✅ Indexed |

To index your repo: visit `https://deepwiki.com/owner/repo`

## GF(3) Triads

| Trit | Skill | Role |
|------|-------|------|
| ⊖ (-1) | hatchery-papers | Validator |
| ○ (0) | **deepwiki-mcp** | Coordinator |
| ⊕ (+1) | bmorphism-stars | Generator |

```
hatchery-papers⊖ ⊗ deepwiki-mcp○ ⊗ bmorphism-stars⊕ = 0 ✓
```

## See Also

- `hatchery-papers` - Academic paper research
- `bmorphism-stars` - GitHub stars index
- `acsets-algebraic-databases` - ACSet patterns (also trit 0)
- `random-walk-fusion` - Exploratory synthesis

---

## GF(3) Skill Coloring

| Skill | Trit | Color | Role |
|-------|------|-------|------|
| deepwiki-mcp | ○ (0) | #26D826 | Coordinator |
| skill-creator | ○ (0) | #26D826 | Coordinator |
| gf3-pr-verify | ⊖ (-1) | #3541C7 | Validator |

**Conservation**: Σ = (0) + (0) + (-1) = -1 ≡ 2 (mod 3)

Balancing skill needed: `gay-mcp⊕` or `bmorphism-stars⊕`

```
deepwiki-mcp○ ⊗ gf3-pr-verify⊖ ⊗ gay-mcp⊕ = 0 ✓
```

Thread: ⟨9bb8⟩

---

**Distilled**: 2026-02-04 from multi-agent session histories  
**Source Sessions**: `97f63193`, `55dcf4c5`, `8ab8ca71`, `f78ac74d`
