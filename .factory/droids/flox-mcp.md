---
name: flox-mcp
description: MCP server wrapper for flox CLI operations - environment management via JSON-RPC
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# flox-mcp

MCP server exposing flox CLI operations over JSON-RPC stdio transport.

**Trit**: 0 (ERGODIC) - Coordinator role for environment orchestration

---

## Overview

This skill wraps the flox CLI as an MCP server, enabling AI agents to manage reproducible development environments programmatically. The server communicates via JSON-RPC 2.0 over stdio.

---

## MCP Tools

### flox_activate

Activate a flox environment.

```json
{
  "name": "flox_activate",
  "description": "Activate a flox environment",
  "inputSchema": {
    "type": "object",
    "properties": {
      "directory": { "type": "string", "description": "Path to environment directory" },
      "remote": { "type": "string", "description": "Remote environment (user/env)" }
    }
  }
}
```

### flox_search

Search for packages in the flox catalog.

```json
{
  "name": "flox_search",
  "description": "Search for packages",
  "inputSchema": {
    "type": "object",
    "properties": {
      "query": { "type": "string", "description": "Package search query" }
    },
    "required": ["query"]
  }
}
```

### flox_install

Install a package into the current environment.

```json
{
  "name": "flox_install",
  "description": "Install a package",
  "inputSchema": {
    "type": "object",
    "properties": {
      "package": { "type": "string", "description": "Package name or pkg-path" }
    },
    "required": ["package"]
  }
}
```

### flox_list

List installed packages in the environment.

```json
{
  "name": "flox_list",
  "description": "List installed packages",
  "inputSchema": {
    "type": "object",
    "properties": {
      "directory": { "type": "string", "description": "Environment directory" }
    }
  }
}
```

### flox_services

Manage flox services (start/stop/status/restart).

```json
{
  "name": "flox_services",
  "description": "Manage flox services",
  "inputSchema": {
    "type": "object",
    "properties": {
      "action": { 
        "type": "string", 
        "enum": ["start", "stop", "restar