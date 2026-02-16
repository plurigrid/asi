# Ghidra MCP Skill

Ghidra reverse engineering via GhidraMCP + radare2 MCP with port resurrection.

## Trigger Conditions

- Binary analysis, disassembly, decompilation
- Malware analysis, vulnerability research
- CTF challenges, firmware extraction
- Function renaming, structure recovery

## Port Resurrection

Ports derived from Gay.jl colors (seed 137508):

| Service | Port | Color |
|---------|------|-------|
| ghidra_mcp | 8647 | #223857 |
| radare2_mcp | 8055 | #90EDC7 |

```bash
# Get current port
python3 /Users/bob/ies/port_resurrect.py -s ghidra_mcp
```

## Setup

### 1. Configure Ghidra Extension Port
In Ghidra: **Edit → Tool Options → GhidraMCP HTTP Server → Port: 8647**

### 2. Start MCP Bridge
```bash
python3 /Users/bob/ies/GhidraMCP/bridge_mcp_ghidra.py \
  --ghidra-server http://127.0.0.1:8647/
```

### 3. Or Use radare2 MCP (Already Loaded)
The `mcp__radare2__*` tools are available in this context.

## Available Tools

### radare2 MCP (Active)
```
mcp__radare2__open_file        - Open binary
mcp__radare2__analyze          - Run analysis
mcp__radare2__list_functions   - List functions
mcp__radare2__decompile_function - Decompile
mcp__radare2__list_strings     - Find strings
mcp__radare2__list_imports     - List imports
mcp__radare2__xrefs_to         - Cross-references
mcp__radare2__rename_function  - Rename function
```

### GhidraMCP (When Bridge Running)
- `get_program_info` - Binary info
- `list_functions` - All functions
- `decompile_function` - Pseudocode
- `search_functions` - Find by pattern
- `auto_create_struct` - Structure recovery

## Workflows

### Quick Binary Analysis
```
1. mcp__radare2__open_file "/path/to/binary"
2. mcp__radare2__analyze level=2
3. mcp__radare2__list_functions
4. mcp__radare2__decompile_function address="main"
```

### Malware Triage
```
1. mcp__radare2__open_file 
2. mcp__radare2__list_imports filter="CreateRemoteThread|VirtualAlloc"
3. mcp__radare2__list_strings filter="http|cmd|powershell"
4. mcp__radare2__list_functions filter="crypt|encode|decode"
```

### Vulnerability Hunt
```
1. mcp__radare2__list_functions filter="strcpy|sprintf|gets"
2. mcp__radare2__decompile_function address="vuln_func"
3. mcp__radare2__xrefs_to address="dangerous_call"
```

## Local Binaries

```
/Users/bob/ies/ghidra_12.0_PUBLIC/  - Ghidra installation
/Users/bob/ies/GhidraMCP/           - MCP bridge
```

## GF(3) Conservation

| Component | Trit |
|-----------|------|
| ghidra_mcp | 0 (ERGODIC) |
| radare2_mcp | -1 (MINUS) |
| port_resurrect | +1 (PLUS) |

**Sum**: 0 ✓

## Related Skills

- `reverse-engineering` - Full RE workflow
- `port-resurrection` - Port derivation
- `cantordust-viz` - Binary visualization
- `blackhat-go` - Security techniques


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
