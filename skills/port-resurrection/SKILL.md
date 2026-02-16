# Port Resurrection Markets

Derive service ports from Gay.jl color sequence. Key space reduction via deterministic but externally-unpredictable port assignment.

## Trigger Conditions

- User mentions port configuration, service discovery
- Starting MCP servers, Ghidra, NATS, or other networked services
- Security through port unpredictability
- Behavior resurrection across worlds (same seed = same ports)

## Core Concept

```
Port = 8000 + (color_int % 2000)
```

Each service gets a color index. Same seed + index = same port across all instances.

**Without seed**: Attacker must scan 2000 ports per service.
**With seed**: Deterministic resurrection across worlds.

## Quick Reference

```bash
# Show all port assignments
python3 /Users/bob/ies/port_resurrect.py

# Source into shell (auto-export all ports)
eval $(python3 /Users/bob/ies/port_resurrect.py --export)

# Generate MCP config
python3 /Users/bob/ies/port_resurrect.py --mcp

# Rotate to next color set
python3 /Users/bob/ies/port_resurrect.py --seed $(date +%s)

# Specific service
python3 /Users/bob/ies/port_resurrect.py -s ghidra_mcp
```

## Shell Integration

```bash
# Add to ~/.zshrc
source /Users/bob/ies/port_resurrect_hook.sh

# Available commands:
port_resurrect    # Reload ports
port_rotate       # Advance to next color
port_show         # Display table
port_of ghidra    # Get specific port
port_start ghidra # Start service on its port
port_discover     # Find running services
```

## Service Registry

| Service | Color Index | Env Var |
|---------|-------------|---------|
| ghidra_mcp | 1 | GHIDRA_MCP_PORT |
| radare2_mcp | 2 | RADARE2_MCP_PORT |
| nats | 3 | NATS_PORT |
| localsend | 4 | LOCALSEND_PORT |
| duckdb_http | 5 | DUCKDB_HTTP_PORT |
| gay_mcp | 6 | GAY_MCP_PORT |
| catcolab | 7 | CATCOLAB_PORT |
| music_topos | 8 | MUSIC_TOPOS_PORT |
| tailscale_derp | 9 | TAILSCALE_DERP_PORT |
| arkhai | 10 | ARKHAI_PORT |
| exo | 11 | EXO_PORT |
| iroh | 12 | IROH_PORT |

## Nickel Integration

```bash
# Regenerate Nickel config
python3 /Users/bob/ies/port_resurrect.py --nickel

# Evaluate
nickel eval /Users/bob/ies/port_resurrection.ncl
```

## Flox Activation

Add to `.flox/env/manifest.toml`:

```toml
[hook]
on-activate = """
  eval $(python3 /Users/bob/ies/port_resurrect.py --export)
"""
```

## MCP Config Generation

```bash
# Generate and merge with existing config
python3 /Users/bob/ies/port_resurrect.py --mcp >> ~/.config/amp/servers.json
```

## GF(3) Trit Assignment

| Component | Trit | Role |
|-----------|------|------|
| port_resurrect.py | 0 | ERGODIC - coordinator |
| port_resurrection.ncl | +1 | PLUS - config generation |
| port_resurrect_hook.sh | -1 | MINUS - shell integration |

**Sum**: 0 ✓ (GF(3) conserved)

## Files

- `/Users/bob/ies/port_resurrect.py` - Python implementation
- `/Users/bob/ies/port_resurrect.bb` - Babashka implementation (faster)
- `/Users/bob/ies/port_resurrection.ncl` - Nickel config
- `/Users/bob/ies/port_resurrect_hook.sh` - Shell hook
- `/Users/bob/ies/port_resurrect_flox.toml` - Flox manifest
- `~/.gay_port_state.json` - Persistent state

## Command Reference

```bash
# Show all ports (either works, bb is faster)
bb /Users/bob/ies/port_resurrect.bb
python3 /Users/bob/ies/port_resurrect.py

# Export to shell
eval $(bb /Users/bob/ies/port_resurrect.bb --export)

# Discover listening ports
python3 /Users/bob/ies/port_resurrect.py --discover

# Check for conflicts
python3 /Users/bob/ies/port_resurrect.py --conflicts

# Generate MCP config
python3 /Users/bob/ies/port_resurrect.py --mcp

# Generate Nickel
python3 /Users/bob/ies/port_resurrect.py --nickel

# Show flox manifest
python3 /Users/bob/ies/port_resurrect.py --flox
```

## Related Skills

- `gay-mcp` - Color generation
- `nickel` - Configuration language
- `ghidra-mcp` - Reverse engineering
- `localsend-mcp` - P2P transfer
- `shell-guard` - Safe shell execution


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
