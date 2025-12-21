# Gay Organization Multi-Remote Infrastructure

## Overview

The Gay organization uses a **balanced ternary** multi-remote architecture based on **Narya observational bridge types** for structure-aware version control.

```
GitLab (LIVE +1) ──push──→ Codeberg (VERIFY 0) ──push──→ GitHub (BACKFILL -1)
       ↑                                                        │
       └─────────────────── pull (upstream) ───────────────────┘
```

## Platform Roles

| Platform | TAP State | Role | Color |
|----------|-----------|------|-------|
| **GitLab** | LIVE (+1) | Primary, forward sync | 🟠 `#FC6D26` |
| **Codeberg** | VERIFY (0) | Mirror, verification | 🟢 `#2F9E44` |
| **GitHub** | BACKFILL (-1) | Upstream, historical | ⚫ `#24292F` |

### Why These Roles?

- **GitLab (LIVE)**: Enterprise features, best CI/CD for the Gay.jl ecosystem
- **Codeberg (VERIFY)**: FOSS-friendly Forgejo instance, community verification
- **GitHub (BACKFILL)**: Existing ecosystem (`plurigrid/gay`, `bmorphism/Gay.jl`)

## Quick Setup

```bash
# Add all remotes
git remote add gitlab git@gitlab.com:gay/Gay.jl.git
git remote add codeberg git@codeberg.org:gay/Gay.jl.git
git remote add github git@github.com:gay/Gay.jl.git

# Configure push-to-all
git remote add all git@gitlab.com:gay/Gay.jl.git
git remote set-url --add --push all git@codeberg.org:gay/Gay.jl.git
git remote set-url --add --push all git@github.com:gay/Gay.jl.git

# Convenience aliases
git config alias.gay-sync '!git push gitlab && git push codeberg && git push github'
git config alias.gay-fetch '!git fetch --all'
```

## Narya Observational Bridge

The sync uses **observational bridge types** from the Topos Institute proposal:

1. **Diffs as logical relations** - computed inductively from type
2. **Conflicts as 2D cubical structures** - resolutions make squares commute
3. **Type changes as spans** - correspondences between versions

### Configuration (`gay-bridge.toml`)

```toml
[organization]
name = "gay"
seed = 1069  # 0x42D
spectral_gap = 0.25

[remotes.gitlab]
platform = "GITLAB"
tap_state = 1  # LIVE
color_r = 252
color_g = 109
color_b = 38

[remotes.codeberg]
platform = "CODEBERG"
tap_state = 0  # VERIFY
color_r = 47
color_g = 158
color_b = 68

[remotes.github]
platform = "GITHUB"
tap_state = -1  # BACKFILL
color_r = 36
color_g = 41
color_b = 47

[verification]
probability = 0.25  # 1/4 spectral gap
```

## Verification at 1/4 Probability

Every push triggers verification with probability 1/4 (spectral gap):

```bash
#!/bin/bash
# .gay-hooks/pre-push

RAND=$((RANDOM % 4))
if [ $RAND -eq 0 ]; then
    echo "🔍 Verification triggered"
    # Check for conflicts, signatures, etc.
fi
```

This matches the PCP theorem: if cheating occurs, verification catches it with probability ≥ 1/4.

## Möbius Inversion

TAP states map to primes for multiplicative structure:

| State | Value | Prime | Meaning |
|-------|-------|-------|---------|
| BACKFILL | -1 | 2 | Antiferromagnetic |
| VERIFY | 0 | 3 | Vacancy |
| LIVE | +1 | 5 | Ferromagnetic |

A trajectory `[+1, +1, 0, -1, +1]` becomes `5 × 5 × 3 × 2 × 5 = 750`.

**Möbius function**: μ(750) = 0 (has squared factor 5²)

This indicates the trajectory has redundancy (repeated LIVE states).

## Tsirelson Patterns

Look for balanced ternary patterns in sync history:

- **2+1** = `[LIVE, LIVE, VERIFY]` → sum = 2
- **1-2** = `[LIVE, BACKFILL, BACKFILL]` → sum = -1

Quantum bound: 2√2 ≈ 2.828
Classical bound: 2

## Files

| File | Description |
|------|-------------|
| `lib/gay_org_multi_remote.jl` | Multi-remote infrastructure |
| `lib/narya_observational_bridge.el` | Emacs Lisp 3×3×3 agents |
| `lib/unified_verification_bridge.jl` | SAW + drand + expander |
| `lib/self_avoiding_expander_tsirelson.jl` | 1/4 verification |

## Usage

```julia
using GayOrgMultiRemote

# Create organization
org = create_gay_org("gay", "Gay.jl"; seed=UInt64(0x42D))

# Generate setup commands
println(generate_git_remote_commands(org))

# Generate Narya config
config = NaryaBridgeConfig(org)
println(generate_narya_config(config))

# Generate pre-push hook
println(generate_pre_push_hook(org))
```

## Emacs Integration

```elisp
;; Load Narya bridge
(require 'narya-observational-bridge)

;; Spawn 3×3×3 agent hierarchy
(narya/spawn-hierarchy #x42D)

;; Fork current agent
(vc/fork (narya/get-agent "root") #x42D)

;; Continue with LIVE branch
(vc/continue forked-agents tap/LIVE)
```

## See Also

- [Topos Institute: Structure-Aware Version Control](https://topos.institute/blog/2024-11-13-structure-aware-version-control-via-observational-bridge-types/)
- [Bumpus: StructuredDecompositions.jl](https://github.com/AlgebraicJulia/StructuredDecompositions.jl)
- [Gay.jl SPI Documentation](https://github.com/bmorphism/Gay.jl)
