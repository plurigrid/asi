---
name: deepwiki-mcp
description: DeepWiki MCP server for AI-powered GitHub repository documentation and
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# DeepWiki MCP Skill

> AI-powered documentation and Q&A for any public GitHub repository

**Version**: 1.0.0
**Trit**: 0 (Ergodic - coordinates knowledge retrieval)
**Bundle**: research
**Provider**: Cognition (Devin AI) - Official, Free, No Auth Required

## Overview

DeepWiki MCP provides programmatic access to AI-generated documentation for any public GitHub repository indexed on [DeepWiki.com](https://deepwiki.com/). It enables:

1. **Wiki Structure**: Get table of contents for any repo's documentation
2. **Wiki Contents**: Read AI-generated documentation for specific topics
3. **Ask Questions**: Get AI-powered answers grounded in repository context

## Server Configuration

### Base URL

```
https://mcp.deepwiki.com/
```

### Wire Protocols

| Protocol | URL | Best For |
|----------|-----|----------|
| **SSE** | `https://mcp.deepwiki.com/sse` | Claude, most clients |
| **Streamable HTTP** | `https://mcp.deepwiki.com/mcp` | OpenAI, Cloudflare, Amp |

## Tools

### 1. `read_wiki_structure`

Get the documentation topic tree for a GitHub repository.

```json
{
  "tool": "read_wiki_structure",
  "params": {
    "repo_owner": "AlgebraicJulia",
    "repo_name": "ACSets.jl"
  }
}
```

Returns: List of documentation topics/sections

### 2. `read_wiki_contents`

Read documentation for a specific topic.

```json
{
  "tool": "read_wiki_contents",
  "params": {
    "repo_owner": "AlgebraicJulia",
    "repo_name": "ACSets.jl",
    "topic": "Overview"
  }
}
```

Returns: AI-generated documentation content

### 3. `ask_question`

Ask any question about a repository with AI-powered, context-grounded response.

```json
{
  "tool": "ask_question",
  "params": {
    "repo_owner": "AlgebraicJulia",
    "repo_name": "Catlab.jl",
    "question": "How do wiring diagrams compose?"
  }
}
```

Returns: AI-powered answer with repository context

## Client Configuration

### Amp / Codex (.mcp.json)

```json
{
  "mcpServers": {
    "deepwiki": {
      "serverUrl": "https://mcp.deepwiki.com