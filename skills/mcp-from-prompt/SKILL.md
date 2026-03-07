---
name: mcp-from-prompt
description: Generate a complete MCP server + skill from an API description, following the ExoPriors Scry prompt pattern. Use when building a new MCP server for any REST API or data source.
version: 1.0.0
---

# MCP-from-Prompt

Generate a production-ready MCP server + Claude skill from an API description. Follows the ExoPriors Scry pattern — the most effective prompt format for agent-API interaction.

## When to Use

- User wants to wrap a REST API as an MCP server
- User has an API they want Claude to use via tools
- User says "make an MCP for X" or "create a skill for Y API"

## Prompt Sources

The API description / prompt can come from:

### Local file
```
/mcp-from-prompt ~/docs/my-api-spec.md
```

### LAN URL (http://, any port)
```
/mcp-from-prompt http://10.1.10.107:8080/prompt.md
/mcp-from-prompt http://conversation-logger:5000/api/spec
/mcp-from-prompt http://192.168.1.50:3000/openapi.json
```

### Tailscale URL
```
/mcp-from-prompt http://thoughtspace:8080/prompt.md
```

### Fetch procedure
When the argument looks like a URL (`http://` or `https://`):
1. Use `curl -sS --connect-timeout 5` (LAN URLs) or WebFetch (public URLs)
2. If JSON, treat as OpenAPI spec
3. If markdown/text, treat as free-form API description
4. Parse into the effective format below

This means you can run a simple HTTP server on any LAN machine:
```bash
# On the remote machine:
cd /path/to/prompts && python -m http.server 8080
# Then from Claude Code:
/mcp-from-prompt http://that-machine:8080/my-api.md
```

## The Effective Format (4 files)

Every generated skill produces exactly 4 files:

### 1. `SKILL.md` — The Skill Registration

This makes it a proper `/skill-name` command in Claude Code.

```markdown
---
name: {kebab-name}
description: {One sentence: what this skill does and when to trigger it.}
version: 1.0.0
---

# {Service Name}

{2-3 sentence summary of what the MCP tools do and what data they access.}

## Tools Available

- `{service}_{verb1}` — {what it does}
- `{service}_{verb2}` — {what it does}

## Quick Patterns

### {Most common use case}
1. Call `{service}_{verb1}` with `{param}`
2. Use result to call `{service}_{verb2}`

### {Second use case}
1. ...

## Reference

See [instructions.md](instructions.md) for full schema, API reference, and gotchas.
```

#### SKILL.md Rules
- Under 80 lines — this loads into every conversation where the skill triggers
- Link to `instructions.md` for details — agent reads it on demand
- List tools by name so the agent knows what's available without loading the MCP
- Quick Patterns = the 2-3 things the user will ask for 90% of the time

### 2. `instructions.md` — The Agent Prompt

This is the prompt engineering core. Structure EXACTLY as follows:

```markdown
# {Service Name} — {One-Liner Purpose}

{Single sentence: what + scale + sources.}

## API Quick Reference

| Method | Endpoint | Content-Type | Body |
|--------|----------|--------------|------|
| POST | `/v1/...` | `text/plain` | Raw payload |
| POST | `/v1/...` | `application/json` | `{"field":"..."}` |
| GET  | `/v1/...` | — | — |

**Base URL**: `https://api.example.com`
**Auth**: `Authorization: Bearer {token_name}`

### Limits
- {Concrete limit 1}
- {Concrete limit 2}

## Core Schema

### {primary_table}
| Column | Type | Notes |
|--------|------|-------|
| id | UUID | PK |
| ... | ... | {Essential context only} |

### {secondary_table}
| Column | Type | Notes |
|--------|------|-------|

### Pre-indexed Views (fast paths)
- **{category}**: `view_a`, `view_b`, `view_c`
- **{category}**: `view_d`, `view_e`

## Key Operations

### Pattern: {most common operation}
```{lang}
{Concrete, copy-pasteable example}
```

### Pattern: {second most common}
```{lang}
{Concrete example}
```

### Pattern: {advanced composition}
```{lang}
{Example combining multiple operations}
```

## Gotchas

1. **{Short name}**: {One sentence explaining the trap + fix.}
2. **{Short name}**: {One sentence.}
3. ...
```

#### Why This Format Works

| Element | Purpose |
|---------|---------|
| **Table-driven API ref** | Agent parses tables faster than prose |
| **Schema with Notes column** | Encodes domain knowledge inline, not separate docs |
| **Pre-indexed views** | Safe starting points — agent picks these first |
| **Pattern sections** | Copy-paste templates beat abstract descriptions |
| **Gotchas (numbered)** | Prevents known failure modes before they happen |

#### Anti-patterns to Avoid

- No tutorials or explanations of concepts
- No "Overview" or "Introduction" sections
- No installation instructions
- No version history
- No links to external docs (they can't follow them)
- Never describe what a tool "could" do — show what it DOES

### 3. `{name}_mcp.py` — The MCP Server

Structure:

```python
"""
{Service} MCP Server — stdio transport.

Wraps the {Service} API as {N} MCP tools:
  {tool_1}, {tool_2}, ...

Run:  python {name}_mcp.py
"""

from __future__ import annotations
import json, ssl, sys, os
from typing import Any
import httpx
from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp.types import TextContent, Tool

# --- Constants ---
BASE_URL = os.environ.get("{NAME}_BASE_URL", "https://api.example.com")
API_KEY = os.environ.get("{NAME}_API_KEY", "")
AUTH_HEADER = {"Authorization": f"Bearer {API_KEY}"} if API_KEY else {}
TIMEOUT = httpx.Timeout(60.0, connect=10.0)

# --- SSL (Cloudflare compat) ---
def _make_ssl_context() -> ssl.SSLContext:
    ctx = ssl.create_default_context()
    ctx.minimum_version = ssl.TLSVersion.TLSv1_2
    return ctx

# --- HTTP client ---
def _build_client() -> httpx.AsyncClient:
    proxy = os.environ.get("{NAME}_SOCKS_PROXY")
    return httpx.AsyncClient(
        base_url=BASE_URL,
        headers=AUTH_HEADER,
        timeout=TIMEOUT,
        http2=True,
        verify=_make_ssl_context(),
        **({"proxy": proxy} if proxy else {}),
    )

async def _request(
    method: str, path: str, *,
    content: str | None = None,
    json_body: dict[str, Any] | None = None,
    content_type: str | None = None,
) -> dict[str, Any]:
    headers: dict[str, str] = {}
    if content_type:
        headers["Content-Type"] = content_type
    async with _build_client() as client:
        resp = await client.request(
            method, path,
            content=content.encode() if content else None,
            json=json_body, headers=headers,
        )
        resp.raise_for_status()
        return resp.json()

# --- MCP server ---
server = Server("{name}")

@server.list_tools()
async def list_tools() -> list[Tool]:
    return [
        # One Tool() per API endpoint
        # inputSchema: only required fields + most-used optional
        # description: action verb, what it returns
    ]

@server.call_tool()
async def call_tool(name: str, arguments: dict[str, Any]) -> list[TextContent]:
    try:
        # Route to endpoint, return JSON
        ...
    except httpx.HTTPStatusError as exc:
        return [TextContent(type="text", text=f"HTTP {exc.response.status_code}: {exc.response.text}")]
    except Exception as exc:
        return [TextContent(type="text", text=f"Error: {exc}")]

async def main() -> None:
    async with stdio_server() as (read_stream, write_stream):
        await server.run(read_stream, write_stream, server.create_initialization_options())

if __name__ == "__main__":
    import asyncio
    asyncio.run(main())
```

#### MCP Server Rules

- **1 tool per API endpoint** — no combined tools
- **Tool names**: `{service}_{verb}` (e.g., `scry_query`, `scry_embed`)
- **Descriptions**: Start with action verb, say what format returns
- **inputSchema**: Only `required` fields + top 2-3 optional. Use `description` on every field
- **Strip large payloads**: Filter vectors/blobs from results by default, add `include_X` flag
- **Env vars for config**: `{NAME}_BASE_URL`, `{NAME}_API_KEY`, `{NAME}_SOCKS_PROXY`
- **SSL context**: Always include for Cloudflare compat
- **httpx + h2**: Async, HTTP/2, 60s timeout

### 4. `run.sh` — The Shell Wrapper

```bash
#!/bin/sh
unset PYTHONPATH
export {NAME}_API_KEY="$(/Users/alice/.cargo/bin/fnox get {KEY_NAME} --age-key-file /Users/alice/.age/key.txt -c /Users/alice/v/instance-onboarding/fnox.toml)"
exec uvx --from 'mcp[cli]' --with httpx --with h2 python /Users/alice/.claude/skills/{skill-name}/{name}_mcp.py
```

If SOCKS proxy needed, add:
```bash
export {NAME}_SOCKS_PROXY="socks5h://localhost:19050"
```
and add `--with 'httpx[socks]'` to the uvx line.

## Generation Workflow

When asked to create an MCP for a service:

1. **Fetch** — Get the prompt/spec from wherever it lives:
   - **LAN URL**: `curl -sS --connect-timeout 5 'http://10.1.10.107:8080/prompt.md'`
   - **Tailscale URL**: `curl -sS --connect-timeout 5 'http://thoughtspace:8080/spec.json'`
   - **Public URL**: Use WebFetch
   - **Local file**: Read directly
   - **User-provided text**: Use as-is

2. **Distill** — Reduce to the effective format:
   - API table: only endpoints the agent will actually use
   - Schema: only columns that matter for queries
   - Patterns: 3-5 concrete, copy-paste examples
   - Gotchas: things that WILL trip up the agent

3. **Generate** — Write all 4 files to `/Users/alice/.claude/skills/{name}/`:
   - `SKILL.md` (skill registration, <80 lines)
   - `instructions.md` (full agent prompt)
   - `{name}_mcp.py` (MCP server)
   - `run.sh` (shell wrapper)

4. **Register** — Run:
   ```bash
   chmod +x /Users/alice/.claude/skills/{name}/run.sh
   claude mcp add {name} -- /Users/alice/.claude/skills/{name}/run.sh
   ```

5. **Test** — Call each tool once to verify connectivity

## Key Insight

The instructions.md IS the prompt. It is loaded into Claude's context when the skill activates. Every line costs tokens. The format above is optimized for:
- **Parseability**: Tables > prose for structured data
- **Actionability**: Patterns > descriptions for "what do I do"
- **Error prevention**: Gotchas > debugging for known failure modes
- **Token efficiency**: No fluff, no tutorials, no history
