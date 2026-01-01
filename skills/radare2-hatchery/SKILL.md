---
name: radare2-hatchery
description: Radare2 Hatchery
version: 1.0.0
---

# Radare2 Hatchery

---
name: radare2-hatchery
description: MCP server for radare2 binary analysis integration with AI assistants. Decompilation, disassembly, and reverse engineering via MCP protocol.
trit: -1
color: "#D6DB4C"
---

## Overview

**radare2-mcp** provides an MCP server enabling Claude and other AI assistants to perform binary analysis using radare2.

## Features

- **Direct stdin/stdout communication** - Simple MCP transport
- **Binary analysis tools** - Full radare2 capabilities
- **AI assistant integration** - Seamless Claude Desktop support
- **File exploration** - Inspect any binary format
- **Decompilation** - Pseudocode generation via r2ghidra

## Installation

```bash
# Via r2pm (radare2 package manager)
r2pm -Uci r2mcp
```

## Configuration

### Claude Desktop

Edit `~/Library/Application Support/Claude/claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "radare2": {
      "command": "r2pm",
      "args": ["-r", "r2mcp"]
    }
  }
}
```

### Docker

```bash
docker build -t r2mcp .
```

```json
{
  "mcpServers": {
    "radare2": {
      "command": "docker",
      "args": ["run", "--rm", "-i", "-v", "/tmp/data:/data", "r2mcp"]
    }
  }
}
```

## MCP Tools Available

The server exposes radare2 analysis via MCP:

- `open_file` - Open binary for analysis
- `analyze` - Run analysis at depth levels 0-4
- `decompile_function` - Get C-like pseudocode
- `list_functions` - Enumerate discovered functions
- `list_strings` - Extract strings from binary
- `xrefs_to` - Find cross-references
- `run_command` - Execute raw r2 commands

## Gay.jl Integration

```julia
# Rec2020 wide gamut learning
gay_seed!(0xe72b09cb7aebe913)

# Forward mode autodiff
∂params = Enzyme.gradient(Forward, loss, params, seed)
```

## Repository

- **Source**: TeglonLabs/radare2-mcp
- **Seed**: `0xe72b09cb7aebe913`
- **Index**: 55/1055
- **Color**: #b3a6b8

## GF(3) Triad

```
radare2-hatchery (-1) ⊗ mcp-builder (0) ⊗ gay-mcp (+1) = 0 ✓
```

## Related Skills

- `mcp-builder` - MCP server development
- `blackhat-go` - Security techniques
- `tree-sitter` - AST-based code analysis
