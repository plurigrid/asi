# Tripartite Agent Allocation

> *GF(3)-balanced skill distribution for parallel execution*

## Overview

Skills are allocated across 3 agents such that `sum(trits) ≡ 0 (mod 3)`.

```
┌─────────────────────────────────────────────────────────────────────┐
│  MINUS (-1)          ERGODIC (0)           PLUS (+1)               │
│  Purple, 270°        Cyan, 180°            Orange, 30°             │
│                                                                     │
│  ┌─────────────┐     ┌─────────────┐       ┌─────────────┐         │
│  │ Constraint  │     │ Balance     │       │ Generative  │         │
│  │ Verification│     │ Flow        │       │ Exploration │         │
│  │ Error Check │     │ Equilibrium │       │ Creation    │         │
│  └─────────────┘     └─────────────┘       └─────────────┘         │
│                                                                     │
│  bisimulation-game   unwiring-arena        gay-mcp                 │
│  spi-parallel-verify acsets                triad-interleave        │
│  polyglot-spi        skill-dispatch        world-hopping           │
│  nix-acset-worlding  bumpus-narratives     agent-o-rama            │
│  structured-decomp   entropy-sequencer     cognitive-superpos      │
│  three-match         tripartite-decomp     skill-evolution         │
└─────────────────────────────────────────────────────────────────────┘
```

## Agent Specifications

### MINUS Agent (trit = -1)

| Skill | Purpose |
|-------|---------|
| `bisimulation-game` | Attacker/Defender/Arbiter verification |
| `spi-parallel-verify` | Strong Parallelism Invariance checking |
| `polyglot-spi` | Cross-language SPI verification |
| `nix-acset-worlding` | Nix store dependency verification via ACSets |
| `structured-decomp` | Sheaves on tree decompositions (FPT) |
| `three-match` | 3-SAT reduction via colored subgraph isomorphism |

**Role**: Constraint verification, error detection, falsification

### ERGODIC Agent (trit = 0)

| Skill | Purpose |
|-------|---------|
| `unwiring-arena` | Play/Coplay autopoietic closure |
| `acsets` | Algebraic database schemas |
| `skill-dispatch` | GF(3) triadic routing |
| `entropy-sequencer` | Information-gain ordering |
| `bumpus-narratives` | Sheaves on time categories for temporal reasoning |
| `tripartite-decompositions` | GF(3)-balanced structured decompositions |

**Role**: Balance, flow, coordination, arena equilibrium

### PLUS Agent (trit = +1)

| Skill | Purpose |
|-------|---------|
| `gay-mcp` | Deterministic color generation |
| `triad-interleave` | 3-stream scheduling |
| `world-hopping` | Badiou possible world navigation |
| `agent-o-rama` | Pattern extraction and learning |
| `skill-evolution` | Evolutionary skill fitness and mutation |

**Role**: Generative exploration, color generation, world navigation

## GF(3) Conservation

Each triplet of operations must satisfy:

```
trit(MINUS) + trit(ERGODIC) + trit(PLUS) = (-1) + 0 + 1 = 0 ≡ 0 (mod 3)
```

## Installation

```bash
# Install all arena skills to codex
npx ai-agent-skills install plurigrid/asi --agent codex

# Or individual skills
npx ai-agent-skills install unwiring-arena --agent codex
npx ai-agent-skills install gay-mcp --agent claude
npx ai-agent-skills install bisimulation-game --agent cursor
```

## Thread History

| Thread | Messages | Pattern |
|--------|----------|---------|
| [GayUncommonsSimulator](https://ampcode.com/threads/T-019b22bf) | 61 | ID = hash(internal ⊻ external) |
| [GAY protocol + open games](https://ampcode.com/threads/T-019b22cd) | 39 | 3-coloring guarantees |
| [DiscoHy operadic](https://ampcode.com/threads/T-019b44e5) | 55 | ParaLens, equilibria |
| [Load acset skill](https://ampcode.com/threads/T-019b43a6) | 88 | C-set as functor |
| [P2P + skills](https://ampcode.com/threads/T-019b4464) | 162 | DiscoPy operads |

## WEV Formula

```julia
WEV(agent, world) = base_value × staleness_mult × scarcity_mult

where:
  base_value     = agent.discrepancy × 10.0
  staleness_mult = 1.0 + Σ(days_since_asked) × 0.1
  scarcity_mult  = 1.0 + (1.0 - occupancy[color] / total)
```

## See Also

- [unwiring-arena SKILL.md](skills/unwiring-arena/SKILL.md)
- [gay-mcp SKILL.md](skills/gay-mcp/SKILL.md)
- [GayUncommonsSimulator.jl](/Users/bob/ies/GayUncommonsSimulator.jl)
