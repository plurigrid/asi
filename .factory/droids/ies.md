---
name: ies
description: ies
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ies

> FloxHub `bmorphism/ies` - Clojure/Julia/Python/multimedia environment with Gay.jl coloring, Flox composition, and DuckDB social analysis.

**Trit Assignment**: 0 (ERGODIC) - Coordinator role for environment orchestration.

**Canonical Triads**:
```
polyglot-spi (-1) ⊗ ies (0) ⊗ gay-mcp (+1) = 0 ✓  [Environment]
three-match (-1) ⊗ ies (0) ⊗ pulse-mcp-stream (+1) = 0 ✓  [Social Analysis]
influence-propagation (-1) ⊗ ies (0) ⊗ agent-o-rama (+1) = 0 ✓  [Cognitive Surrogate]
```

---

## Quick Start

```bash
# Activate from FloxHub
flox activate -r bmorphism/ies

# Or clone locally
flox pull -r bmorphism/ies ~/ies
flox activate -d ~/ies

# Verify Gay.jl integration
echo $GAY_SEED      # 69
echo $GAY_PORT      # 42069
```

---

## Installed Packages (10)

| Package | Version | Description |
|---------|---------|-------------|
| babashka | 1.12.208 | Clojure scripting (no JVM startup) |
| clojure | 1.12.2.1565 | JVM Lisp |
| jdk | 21.0.8 | OpenJDK |
| julia-bin | 1.11.7 | Technical computing |
| ffmpeg | 7.1.1 | Media processing |
| python312 | 3.12.11 | Python interpreter |
| coreutils | 9.8 | GNU utilities |
| tailscale | 1.88.4 | Mesh VPN |
| enchant2 | 2.6.9 | Spell checking |
| pkg-config | 0.29.2 | Build configuration |

---

## Environment Composition

### Include Syntax

Compose environments via `manifest.toml`:

```toml
[include]
environments = [
  # FloxHub remote environments
  { remote = "bmorphism/effective-topos" },
  { remote = "flox/python-dev" },
  
  # Local environments (relative or absolute path)
  { dir = "../shared-tools" },
  { dir = "/Users/bob/.flox/environments/common" },
]
```

### Merge Rules by Section

| Section | Merge Behavior |
|---------|----------------|
| `[install]` | **Union** - packages from all envs combined |
| `[vars]` | **Last wins** - later env overrides earlier |
| `[hook]` | **Concatenate** - all on-activate scripts run in order |
| `[profile]` | **Concatenate** - all shell init scripts run in order |
| `[services]` | 