---
name: hatchery-index
description: Index of 1057 hatchery repos with GAY.md color assignments. Maps plurigrid/bmorphism/TeglonLabs ecosystem to skills.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Hatchery Index

> *1057 repos. 1055 GAY.md files. One color lattice.*

## Repository Statistics

| Owner | Repos | Primary Focus |
|-------|-------|---------------|
| plurigrid | 557 | Infrastructure, protocols |
| bmorphism | 405 | Research, Julia, category theory |
| TeglonLabs | 63 | MCP servers, tooling |
| Tritwies | 11 | Formal methods |
| Others | 21 | Various |

## Key Skill-Ready Repos

| # | Repo | Hex | Skill Potential |
|---|------|-----|-----------------|
| 1 | bmorphism/Gay.jl | #B0285F | Core color generation |
| 2 | bmorphism/GayMonteCarloMeasurements.jl | #77DEB1 | Stochastic coloring |
| 3 | bmorphism/CatColab | #8ADB6E | Collaborative categories |
| 4 | TeglonLabs/narya | #3A71C0 | HOTT proof assistant |
| 5 | TeglonLabs/mcp-server-tree-sitter | #2A7AE3 | AST parsing MCP |
| 6 | TeglonLabs/radare2-mcp | #D6DB4C | Binary analysis MCP |
| 7 | TeglonLabs/chroma | #6638C2 | Color utilities |
| 8 | TeglonLabs/topoi | #AF100A | Topos theory |
| 9 | TeglonLabs/ohy | #AD90E0 | Hy language tools |
| 10 | TeglonLabs/Stahl | #C30F2D | Steel→Stahl translation |
| 11 | TeglonLabs/topOS | #969D34 | Topos-based OS |
| 12 | TeglonLabs/joker | #61BFE7 | Clojure linter |
| 13 | TeglonLabs/bison | #79EBDD | Parser generator |
| 14 | TeglonLabs/deepwiki-mcp | #D7D085 | DeepWiki MCP |
| 15 | plurigrid/ACSets.jl | #E146A8 | Attributed C-Sets |
| 16 | plurigrid/AlgebraicRewriting.jl | #0BAD20 | DPO rewriting |

## GAY.md Structure

Each repo contains GAY.md with:

```markdown
# GAY - Gamut-Aware Yielding

> **Repo Color:** `#XXXXXX` | **Seed:** `0x...` | **Index:** N/1055

## Chromatic Identity
Global Fingerprint: 0x...
Global Color: #...
This Repo: #... (index N)
```

## Usage

```bash
# Find repos by pattern
ls /Users/bob/ies/hatchery_repos | grep -i pattern

# Read GAY.md for color
head -20 /Users/bob/ies/hatchery_repos/owner__repo/GAY.md

# Count by owner
ls /Users/bob/ies/hatchery_repos | cut -d'_' -f1 | sort | uniq -c | sort -rn
```

## Creating Skills from Hatc