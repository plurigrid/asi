---
name: bmorphism-interactome
description: GitHub interactome explorer for bmorphism/plurigrid ecosystem. Maps collaborations across AlgebraicJulia, Topos Institute, Anthropic, and MCP servers. Use for discovering cobordisms between research communities.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# bmorphism-interactome Skill

> *Mapping the cobordisms between research communities via shared contributors*

## Profile: bmorphism (Barton Rhodes)

```
@bmorphism | 255 followers | 1.6k following
@plurigrid founder | San Francisco
"Parametrised optics model cybernetic systems"
```

## Core Repositories

| Repo | Stars | Description | Trit |
|------|-------|-------------|------|
| [Gay.jl](https://github.com/bmorphism/Gay.jl) | 3 | Wide-gamut color sampling + SPI | 0 |
| [agent-o-shiva](https://github.com/bmorphism/agent-o-shiva) | - | Rama agent platform fork | 0 |
| [GeoACSets.jl](https://github.com/bmorphism/GeoACSets.jl) | - | Categorical GIS | 0 |
| [bafishka](https://github.com/bmorphism/bafishka) | 1 | Fish + Steel Clojure | -1 |
| [ocaml-mcp-sdk](https://github.com/bmorphism/ocaml-mcp-sdk) | 60 | OCaml MCP SDK | -1 |
| [babashka-mcp-server](https://github.com/bmorphism/babashka-mcp-server) | 16 | Babashka MCP | -1 |
| [multiverse-color-game](https://github.com/bmorphism/multiverse-color-game) | - | VisionPro holographic | +1 |

## Plurigrid Organization (542 repos)

```
plurigrid: "building for a more agentic mesoscale 🦆"
├── asi/                    # "everything is topological chemputer!"
├── UnwiringDiagrams.jl     # Worlding/Unworlding Uexküll
├── vcg-auction/            # VCG auctions in Rust
├── microworlds/            # Agent simulations
├── risc0-cosmwasm/         # zkVM + CosmWasm
└── skillz/                 # Anthropic skills fork
```

## Interactome Clusters

### Cluster 1: Topos Institute ↔ AlgebraicJulia

**Bridge Authors:**
- `olynch` - poly, Catlab.jl, ACSets.jl
- `epatters` - Catlab lead, Topos
- `kasbah` - Senior engineer @ Topos

**Cobordism:**
```
plurigrid/UnwiringDiagrams.jl ←fork← AlgebraicJulia/WiringDiagrams.jl
           ↓                                    ↓
    "Umwelt Worlding"                   Compositional Systems
           ↓                                    ↓
      Gay.jl SPI ←───────────────────→ ToposInstitute/poly
```
