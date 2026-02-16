# MCP Server Inventory: Cross-Platform Discovery

## Discovery Sources

| Source | Config File | MCPs Found |
|--------|-------------|------------|
| **Codex** | `~/.codex/config.toml` | firecrawl, huggingface, marginalia, radare2, tree-sitter, unison, gay |
| **Crush** | `.crush.json` | gay, tree-sitter, babashka, exa, verses |
| **Amp** | `~/.amp/package/` | (via skills) |
| **Claude** | `~/.claude/settings.json` | (via plugins) |

---

## MCP Server Catalog

### 1. GAY.jl (Deterministic Colors)
```toml
[mcp_servers.gay]
command = "julia"
args = ["--project=/Users/bob/ies/rio/GayMCP", "/Users/bob/ies/rio/GayMCP/bin/gay-mcp"]
```
**Tools**: `generate_color`, `generate_palette`, `verify_gf3`, `seed_chain`
**Trit**: 0 (ERGODIC) - core color system

### 2. Firecrawl (Web Scraping)
```toml
[mcp_servers.firecrawl]
url = "https://mcp.firecrawl.dev/fc-ef01f1d6d3b544a38363e4444b97e07b/v2/mcp"
```
**Tools**: `scrape`, `crawl`, `map`, `search`, `extract`
**Trit**: +1 (PLUS) - generates content from web

### 3. Exa (AI Search)
```json
{
  "type": "http",
  "url": "https://mcp.exa.ai/mcp?tools=web_search_exa,crawling_exa,..."
}
```
**Tools**: `web_search_exa`, `crawling_exa`, `deep_researcher_start`
**Trit**: +1 (PLUS) - generates search results

### 4. HuggingFace (ML Models)
```toml
[mcp_servers.huggingface]
command = "node"
args = ["hf-mcp-server/packages/app/dist/server/stdio.js"]
```
**Tools**: `model_search`, `dataset_search`, `paper_search`, `space_search`, `hf_doc_search`
**Trit**: 0 (ERGODIC) - navigates model space

### 5. Tree-Sitter (Code Analysis)
```toml
[mcp_servers.tree-sitter]
command = "uv"
args = ["run", "-m", "mcp_server_tree_sitter.server"]
```
**Tools**: `get_ast`, `run_query`, `find_usage`, `analyze_complexity`
**Trit**: -1 (MINUS) - validates/analyzes code structure

### 6. Radare2 (Binary Analysis)
```toml
[mcp_servers.radare2]
command = "r2pm"
args = ["-r", "r2mcp"]
```
**Tools**: `open_file`, `analyze`, `disassemble`, `decompile_function`, `list_functions`
**Trit**: -1 (MINUS) - reverse engineers binaries

### 7. Marginalia (Indie Search)
```toml
[mcp_servers.marginalia]
command = "node"
args = ["marginalia-mcp-server/build/index.js"]
```
**Tools**: `search-marginalia`
**Trit**: +1 (PLUS) - indie web search

### 8. Babashka (Clojure Scripting)
```json
{
  "command": "npx",
  "args": ["-y", "@mseep/babashka-mcp-server"]
}
```
**Tools**: `run_script`, `eval_expr`
**Trit**: 0 (ERGODIC) - executes Clojure

### 9. Unison (Content-Addressed Code)
```toml
[mcp_servers.unison]
command = "ucm"
args = ["mcp"]
```
**Tools**: `find`, `view`, `add`, `update`
**Trit**: 0 (ERGODIC) - content-addressed transport

### 10. Verses (Verse Language)
```json
{
  "command": "verse",
  "args": ["mcp", "serve"]
}
```
**Tools**: TBD
**Trit**: 0 (ERGODIC)

---

## Trit Assignments Summary

| Trit | MCPs | Role |
|------|------|------|
| **-1 (MINUS)** | tree-sitter, radare2 | Analyze, validate, reverse |
| **0 (ERGODIC)** | gay, huggingface, babashka, unison, verses | Transport, derive, navigate |
| **+1 (PLUS)** | firecrawl, exa, marginalia | Generate, search, scrape |

---

## Usage Frequency (from threads)

| MCP | Thread Mentions | Primary Use |
|-----|-----------------|-------------|
| `gay` | 15+ | Color generation, GF(3) verification |
| `firecrawl` | 10+ | Web scraping, content extraction |
| `huggingface` | 8+ | Model/paper search |
| `exa` | 6+ | AI-powered search |
| `tree-sitter` | 5+ | Code analysis, AST queries |
| `radare2` | 3+ | Binary reverse engineering |
| `marginalia` | 2+ | Indie web search |
| `babashka` | 2+ | Clojure scripting |
