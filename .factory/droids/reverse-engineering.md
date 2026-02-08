---
name: reverse-engineering
description: Reverse Engineering Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Reverse Engineering Skill

Binary analysis and reverse engineering via MCP servers for Ghidra, IDA Pro, radare2, and angr.

## Trigger Conditions

- User asks to analyze binaries, disassemble code, decompile functions
- Questions about malware analysis, vulnerability research, CTF challenges
- Binary diffing, patch analysis, firmware extraction
- Symbol recovery, function identification, control flow analysis

## MCP Servers

### 1. GhidrAssistMCP (Ghidra - Free)
**Repository**: https://github.com/jtang613/GhidrAssistMCP  
**Stars**: High activity  
**Transport**: HTTP/SSE on port 8080

**Installation**:
```bash
# Download from releases page
# In Ghidra: File → Install Extensions → Add Extension
# Enable: File → Configure → Configure Plugins → GhidrAssistMCP
```

**31 Built-in Tools**:
| Category | Tools |
|----------|-------|
| Program Analysis | `get_program_info`, `list_functions`, `list_data`, `list_strings`, `list_imports`, `list_exports`, `list_segments` |
| Function Analysis | `get_function_info`, `decompile_function`, `disassemble_function`, `function_xrefs`, `search_functions` |
| Navigation | `get_current_address`, `xrefs_to`, `xrefs_from`, `get_current_function` |
| Modification | `rename_function`, `rename_variable`, `set_function_prototype`, `set_local_variable_type`, `set_disassembly_comment` |
| Advanced | `auto_create_struct` |

### 2. LaurieWired/GhidraMCP (Popular Alternative)
**Repository**: https://github.com/LaurieWired/GhidraMCP  
**Transport**: Python bridge to Ghidra

### 3. IDA Pro MCP Servers

**mrexodia/ida-pro-mcp** (Most active):
```bash
git clone https://github.com/mrexodia/ida-pro-mcp
cd ida-pro-mcp
pip install -e .
```

**MxIris-Reverse-Engineering/ida-mcp-server** (473 stars):
```bash
git clone https://github.com/MxIris-Reverse-Engineering/ida-mcp-server
```

**fdrechsler/mcp-server-idapro**:
```bash
git clone https://github.com/fdrechsler/mcp-server-idapro
```

### 4. radare2-mcp (Official)
**Repository**: https://github.com/radar