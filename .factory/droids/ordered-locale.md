---
name: ordered-locale
description: Ordered Locale Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Ordered Locale Skill

**Trit**: +1 (PLUS/GENERATOR)
**GF(3)**: Σ(-1,0,+1) = 0 (conserved)

## Overview

Point-free topology with direction. MCP servers indexed by creation-time color via SplitMix64. Every decision trifurcates into MINUS/ERGODIC/PLUS parallel paths. GF(3) conservation guaranteed on every substrate in every interaction.

Implements Heunen-style ordered locales with observational bridge types in Narya proof assistant. Bridge types model the "way below" relation U ≪ V in ordered locales, providing a foundation for:

- **MCP Locale**: Servers as opens, dependencies as way-below
- Causal structure in topological spaces
- Directed homotopy theory
- Sheaves respecting directional constraints
- GF(3) triadic systems

## Files

| File | Description |
|------|-------------|
| `mcp_locale.py` | Python: MCP ordered locale with triadic decisions |
| `mcp_locale.mo` | Modelica: Acausal model (replaces Wolfram) |
| `narya/ordered_locale.ny` | Core definitions: 𝟚, Bridge, WayBelow, frame ops |
| `narya/gf3.ny` | GF(3) arithmetic and conservation |
| `narya/bridge_sheaf.ny` | Sheaves respecting bridge structure |
| `narya/narya-ordered-locale.el` | Emacs/Proof General integration |
| `ordered_locale.jl` | Julia: Frame operations, cones/cocones |

## MCP Locale

Every MCP server is an **open set** in the locale, indexed by creation-time color:

```python
from mcp_locale import create_mcp_locale, trifurcate_decision

locale = create_mcp_locale(seed=0x42D)
# Each MCP gets deterministic color: seed → SplitMix64 → RGB → hue → trit
```

### Triadic Decisions

Every decision trifurcates into parallel paths:

| Path | Trit | Role | Action |
|------|------|------|--------|
| MINUS | -1 | Validator | Check constraints |
| ERGODIC | 0 | Coordinator | Find optimal route |
| PLUS | +1 | Executor | Generate result |

```python
decision = trifurcate_decision(
    "swap 10 APT",
    seed=0x42D,
    minus_fn=validate,
    ergodic_fn=coordinate,
    plus_fn=execute,
    aggregate_f