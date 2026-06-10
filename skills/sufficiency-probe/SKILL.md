---
name: sufficiency-probe
description: 'Probes context-setting tooling sufficiency at every interaction. Validates world letter, flox activation, Emacs server, open-games-hs reachability, DeepWiki cache, color:// resolution, and loaded skills. Triggers: sufficiency, probe, context check, tooling status, environment validation.'
category: meta
featured: 'false'
trit: '-1'
trit_label: MINUS
verified: 'true'
---

# Sufficiency Probe

**Trit**: -1 (MINUS/validator)
**Role**: Context-setting tooling sufficiency checker
**Invocation**: Run at interaction start to validate working environment

## Description

Probes every dimension of the context-setting tooling stack and emits a terse sufficiency report with checkmarks. This is a validator skill: it does not generate or transform -- it verifies that the preconditions for productive work are met.

## When to Use

- Start of any session to establish context
- After switching worlds (`cd ~/worlds/X`)
- After activating/deactivating flox environments
- Before invoking skills that depend on specific tooling
- When something feels broken and you need a diagnostic

## Probe Checks

### 1. World Letter Detection

Detect which single-letter world is active from `$PWD`:

```bash
# Extract world letter from cwd
WORLD_LETTER=$(pwd | sed -n 's|.*/worlds/\([a-z]\)/.*|\1|p; s|.*/worlds/\([a-z]\)$|\1|p')
if [ -n "$WORLD_LETTER" ]; then
  echo "[ok] world: $WORLD_LETTER"
else
  echo "[--] world: not in a single-letter world dir"
fi
```

### 2. Flox Activation

```bash
# Check FLOX_ENV is set (proves flox activate ran)
if [ -n "$FLOX_ENV" ]; then
  echo "[ok] flox: activated ($FLOX_ENV_DESCRIPTION)"
else
  echo "[--] flox: not activated"
fi
```

### 3. Emacs Server

```bash
# Test if emacsclient can reach a running Emacs
if emacsclient --eval '(+ 1 1)' 2>/dev/null | grep -q '2'; then
  echo "[ok] emacs: server running"
else
  echo "[--] emacs: server not reachable"
fi
```

### 4. open-games-hs Reachability

```bash
# Check source tree exists
if test -d ~/worlds/o/open-games-hs/src; then
  echo "[ok] open-games-hs: src/ reachable"
else
  echo "[--] open-games-hs: src/ not found"
fi
```

### 5. DeepWiki Sources

Check if DeepWiki MCP is available and can resolve repos relevant to current world:

```bash
# DeepWiki is an MCP tool, so test availability by checking the tool list.
# In claude code context, verify mcp__deepwiki__read_wiki_structure is in deferred tools.
# No shell equivalent -- this is checked via tool availability in-session.
echo "[ok] deepwiki: MCP tool available"  # or [--] if not in tool list
```

### 6. color:// Resolution (GAY.json)

```bash
# Check GAY.json exists for current world
WORLD_LETTER=$(pwd | sed -n 's|.*/worlds/\([a-z]\)/.*|\1|p; s|.*/worlds/\([a-z]\)$|\1|p')
if [ -n "$WORLD_LETTER" ] && [ -f "$HOME/worlds/$WORLD_LETTER/GAY.json" ]; then
  echo "[ok] color://: GAY.json present for world $WORLD_LETTER"
else
  echo "[--] color://: GAY.json missing or not in a world"
fi
```

### 7. Skills Loaded vs Needed

Assess which skills are loaded in current session vs which are needed for the detected world context. Core skills that should always be loaded:

| Skill | Always | When |
|-------|--------|------|
| flox | yes | environment management |
| emacs | yes | editor integration |
| open-games | if world=o | game theory work |
| sdf | if coding | flexibility patterns |
| tree-sitter | if coding | AST analysis |

## Combined Probe Script

Run all checks as a single block:

```bash
#!/usr/bin/env bash
# sufficiency-probe: terse environment validation
set -euo pipefail

echo "=== SUFFICIENCY PROBE ==="
echo ""

# 1. World letter
WORLD_LETTER=$(pwd | sed -n 's|.*/worlds/\([a-z]\)/.*|\1|p; s|.*/worlds/\([a-z]\)$|\1|p')
if [ -n "$WORLD_LETTER" ]; then
  echo "[ok] world: $WORLD_LETTER"
else
  echo "[--] world: none (cwd=$(pwd))"
fi

# 2. Flox
if [ -n "${FLOX_ENV:-}" ]; then
  echo "[ok] flox: $FLOX_ENV_DESCRIPTION"
else
  echo "[--] flox: not activated"
fi

# 3. Emacs
if emacsclient --eval '(+ 1 1)' 2>/dev/null | grep -q '2'; then
  echo "[ok] emacs: server running"
else
  echo "[--] emacs: no server"
fi

# 4. open-games-hs
if test -d ~/worlds/o/open-games-hs/src; then
  echo "[ok] open-games-hs: reachable"
else
  echo "[--] open-games-hs: missing"
fi

# 5. DeepWiki -- checked in-session via MCP tool presence
echo "[??] deepwiki: check MCP tool list in session"

# 6. color:// (GAY.json)
if [ -n "$WORLD_LETTER" ] && [ -f "$HOME/worlds/$WORLD_LETTER/GAY.json" ]; then
  echo "[ok] color://: GAY.json for $WORLD_LETTER"
else
  echo "[--] color://: no GAY.json"
fi

echo ""
echo "=== END PROBE ==="
```

## Output Format

Terse. One line per check. Checkmark prefixes:

```
[ok]  = sufficient
[--]  = insufficient / missing
[??]  = cannot determine from shell (needs in-session check)
```

Example output:

```
=== SUFFICIENCY PROBE ===

[ok] world: o
[ok] flox: activated (effective-topos)
[ok] emacs: server running
[ok] open-games-hs: reachable
[ok] deepwiki: MCP tool available
[ok] color://: GAY.json for o
[ok] skills: 5/5 core loaded (sdf, tree-sitter, open-games, flox, emacs)

=== END PROBE ===
```

## In-Session Probe (for Claude Code)

When invoked as a skill inside Claude Code, run the shell probe AND supplement with in-session checks:

1. Execute the combined probe script via Bash tool
2. Check deferred tool list for `mcp__deepwiki__read_wiki_structure` presence
3. Check which `/skill` invocations have occurred in this conversation
4. Emit combined report

## GF(3) Triad

```
sufficiency-probe (-1) + worlding (+1) + glass-bead-game (0) = 0
sufficiency-probe (-1) + skill-finder-verifier (0) + sdf (+1) = 0
```

The probe is MINUS because it only validates -- it never generates or transforms. It is the boundary condition that ensures the generative skills have ground to stand on.

## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 8. Degeneracy

**Concepts**: redundancy, fallback, multiple strategies, robustness

### GF(3) Balanced Triad

```
sufficiency-probe (-) + SDF.Ch8 (-) + [balancer needs +2 mod 3 = -1] = 0
```

**Skill Trit**: -1 (MINUS - verification/validation)

### Connection Pattern

Degeneracy provides multiple implementation strategies with fallback. The sufficiency probe validates which strategies are actually available, enabling degeneracy-aware dispatch.
