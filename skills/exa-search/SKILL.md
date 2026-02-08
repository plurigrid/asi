---
name: exa-search
description: Use Exa for semantic/neural web search. Exa understands context and returns high-quality results. Use this skill when you need to search the web for documentation, research, or any information that requires understanding meaning rather than just keyword matching. NEVER substitute web_search for Exa - they serve completely different purposes.
---

# Exa Semantic Search

Exa provides neural/semantic search via MCP. Use it for high-quality web search that understands context.

## When to Use Exa

- Searching for documentation or technical information
- Research requiring semantic understanding
- Finding information where exact keywords are unknown
- Company research and LinkedIn searches
- Deep research tasks

## When NOT to Use Exa

- Never use `web_search` as a substitute - it's basic keyword matching only
- If Exa fails, troubleshoot Exa - don't fall back to `web_search`

## Available Tools

The Exa MCP server provides these tools:

- `web_search_exa` - Semantic web search
- `crawling_exa` - Crawl and extract web content
- `company_research_exa` - Research companies
- `linkedin_search_exa` - Search LinkedIn profiles
- `deep_researcher_start` - Start deep research task
- `deep_researcher_check` - Check deep research status

## Configuration

Exa is configured as a remote HTTP MCP in `~/.mcp.json`:

```json
{
  "exa": {
    "type": "http",
    "url": "https://mcp.exa.ai/mcp?tools=web_search_exa,crawling_exa,company_research_exa,linkedin_search_exa,deep_researcher_start,deep_researcher_check"
  }
}
```

## Usage Examples

### Basic Search
Use the Exa MCP tools directly when semantic search is needed.

### Deep Research
1. Start with `deep_researcher_start` for complex topics
2. Poll with `deep_researcher_check` until complete
3. Get comprehensive, synthesized results

## Critical Rules

1. **NEVER replace Exa with web_search** - they are fundamentally different
2. **NEVER use web_search in Task sub-agents** as a substitute for Exa
3. If Exa fails, troubleshoot Exa - do not substitute
