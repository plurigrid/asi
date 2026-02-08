# Plurigrid ASI - gay branch

<<<<<<< HEAD
**SplitMixTernary**: GF(3)-balanced splittable random streams extending SplittableRandoms.jl.

## Purpose
=======
<p align="center">
  <strong>Homebrew for AI agent skills.</strong><br>
  Universal Skills installer for any agent that follows the open standard spec 
</p>

<p align="center">
  <img src="https://img.shields.io/badge/skills-38-blue?style=flat-square" alt="Skills" />
  <img src="https://img.shields.io/badge/agents-10+-green?style=flat-square" alt="Compatible Agents" />
  <img src="https://img.shields.io/badge/license-MIT-brightgreen?style=flat-square" alt="License" />
  <img src="https://img.shields.io/npm/v/ai-agent-skills?style=flat-square&color=red" alt="npm" />
  <img src="https://img.shields.io/npm/dt/ai-agent-skills?style=flat-square&color=orange" alt="Downloads" />
</p>
>>>>>>> origin/feature/skill-connectivity-hub-20251226

This branch focuses on **ternary extensions** to splittable random number generation:

1. **SplitMixTernary algorithm** - Three parallel streams with GF(3) conservation
2. **Extension proposal for SplittableRandoms.jl** - `split3()` API
3. **Verified properties** - Dafny + Narya proofs

## Core Algorithm

```julia
# Three streams from one seed
const STREAM_MINUS   = 0x243f6a8885a308d3  # π
const STREAM_ERGODIC = 0xb7e151628aed2a6a  # e  
const STREAM_PLUS    = 0x452821e638d01377  # √2

function split3(seed::UInt64)
    base = splitmix64(seed)
    (
        splitmix64(base ⊻ STREAM_MINUS),   # -1 stream
        splitmix64(base ⊻ STREAM_ERGODIC), #  0 stream
        splitmix64(base ⊻ STREAM_PLUS)     # +1 stream
    )
end
```

## Skill Triads

### SplitMixTernary Triad

| Skill | Trit | Description |
|-------|------|-------------|
| `splitmix-ternary` | 0 | Core ternary RNG algorithm |
| `spi-parallel-verify` | -1 | Verification tooling |
| `triad-interleave` | +1 | Stream interleaving |

**Sum: 0** ✓ GF(3) conserved

### BB(6) Oracle Triad

| Skill | Trit | Description |
|-------|------|-------------|
| `busy-beaver-oracle` | +1 | Generate BB(n) lower bound proofs |
| `levin-levity` | 0 | Nash equilibrium + WEV |
| `prediction-market-oracle` | -1 | Market-making |

**Sum: 0** ✓ GF(3) conserved

## Skills

| Skill | Origin | Description |
|-------|--------|-------------|
| `splitmix-ternary` | new | SplittableRandoms.jl extension |
| `unison-acset` | PR #36 | ACSet-structured docs, seed 1069 |
| `markov-game-acset` | PR #34 | Markov games with derangement |
| `rama-gay-zig` | PR #37 | Gay.jl + Rama + Zig triad |
| `levin-levity` | original | Levin search + WEV extraction |
| `autopoiesis` | original | Self-modifying config |
| `open-games` | original | Compositional game theory |
| `bisimulation-game` | original | Skill dispersal |
| `world-hopping` | original | Possible world navigation |

## SplitMix64 Constants

```
GOLDEN = 0x9e3779b97f4a7c15
MIX1   = 0xbf58476d1ce4e5b9
MIX2   = 0x94d049bb133111eb
SEED   = 0x42D (1069)
```

## Verified Properties

| Property | Dafny | Narya |
|----------|-------|-------|
| Determinism | ✅ `SplitMixTernary.dfy` | ✅ `spi_conservation.ny` |
| Path invariance | ✅ | — |
| GF(3) conservation | ✅ | ✅ `gf3.ny` |
| Reafference closure | ✅ `GayMcpCriticalProofs.dfy` | ✅ |

## SplittableRandoms.jl Extension Proposal

```julia
# Proposed additions to SplittableRandoms.jl

struct SplittableRandom3
    minus::SplittableRandom
    ergodic::SplittableRandom
    plus::SplittableRandom
end

split3(rng::SplittableRandom)::SplittableRandom3
trit(sr3::SplittableRandom3)::Int  # -1, 0, or +1
rand_trit(sr3::SplittableRandom3)::Symbol
```

## Installation

```bash
git clone https://github.com/plurigrid/asi -b gay
cd asi
amp skill splitmix-ternary
```

## Related

- [Gay.jl](https://github.com/bmorphism/Gay.jl) - Reference implementation
- [SplittableRandoms.jl](https://github.com/JuliaMath/SplittableRandoms.jl) - Base library
- [Pigeons.jl](https://pigeons.run) - SPI inspiration

## License

Apache-2.0

---

<<<<<<< HEAD
*"In the ternary splitting, the colors find their balance."*
=======
## Quick Start

```bash
# Browse skills interactively
npx ai-agent-skills browse

# Install from our curated catalog
npx ai-agent-skills install frontend-design

# Install for specific agents
npx ai-agent-skills install frontend-design --agent cursor
npx ai-agent-skills install frontend-design --agent codex
npx ai-agent-skills install frontend-design --agent amp

# Install from any GitHub repo
npx ai-agent-skills install anthropics/skills
npx ai-agent-skills install anthropics/skills/pdf    # specific skill

# Install from local path
npx ai-agent-skills install ./my-custom-skill
```

That's it. The skill installs to the right location for your agent automatically.

## Why This Exists

Every major AI coding agent now supports skills. But they're scattered everywhere.

This repo curates the best in one place. Quality over quantity. All skills follow the [Agent Skills spec](https://agentskills.io).

## Compatible Agents

Works with **Claude Code**, **Cursor**, **Amp**, **VS Code**, **GitHub Copilot**, **Goose**, **Letta**, **OpenCode**, and **Claude.ai**.

## Available Skills

### Development
| Skill | Description |
|-------|-------------|
| `frontend-design` | Production-grade UI components and styling |
| `mcp-builder` | Create MCP servers for agent tool integrations |
| `skill-creator` | Guide for creating new agent skills |
| `code-review` | Automated PR review patterns |
| `code-refactoring` | Systematic code improvement techniques |
| `backend-development` | APIs, databases, server architecture |
| `python-development` | Modern Python 3.12+ patterns |
| `javascript-typescript` | ES6+, Node, React, TypeScript |
| `webapp-testing` | Browser automation and testing with Playwright |
| `database-design` | Schema design and optimization |
| `llm-application-dev` | Build LLM-powered applications |
| `artifacts-builder` | Interactive React/Tailwind web components |
| `changelog-generator` | Generate changelogs from git commits |

### Documents
| Skill | Description |
|-------|-------------|
| `pdf` | Extract, create, merge, split PDFs |
| `xlsx` | Excel creation, formulas, data analysis |
| `docx` | Word documents with formatting |
| `pptx` | PowerPoint presentations |

### Creative
| Skill | Description |
|-------|-------------|
| `canvas-design` | Visual art and poster creation |
| `algorithmic-art` | Generative art with p5.js |
| `image-enhancer` | Improve image quality and resolution |
| `slack-gif-creator` | Create animated GIFs for Slack |
| `theme-factory` | Professional font and color themes |
| `video-downloader` | Download videos from various platforms |

### Business
| Skill | Description |
|-------|-------------|
| `brand-guidelines` | Apply brand colors and typography |
| `internal-comms` | Status updates and team communication |
| `competitive-ads-extractor` | Analyze competitor ad strategies |
| `domain-name-brainstormer` | Generate and check domain availability |
| `lead-research-assistant` | Identify and qualify leads |

### Productivity
| Skill | Description |
|-------|-------------|
| `doc-coauthoring` | Co-author docs, proposals, specs with structured workflow |
| `job-application` | Cover letters and applications using your CV |
| `qa-regression` | Automated regression testing with Playwright |
| `code-documentation` | Generate docs from code |
| `content-research-writer` | Research and write content with citations |
| `developer-growth-analysis` | Track developer growth metrics |
| `file-organizer` | Organize files and find duplicates |
| `invoice-organizer` | Organize invoices for tax prep |
| `meeting-insights-analyzer` | Analyze meeting transcripts |
| `raffle-winner-picker` | Randomly select contest winners |

## Commands

```bash
# Interactive browser (TUI)
npx ai-agent-skills browse

# List all available skills
npx ai-agent-skills list
npx ai-agent-skills list --category development
npx ai-agent-skills list --installed --agent cursor

# Install from catalog, GitHub, or local path
npx ai-agent-skills install <name>                    # from catalog
npx ai-agent-skills install <owner/repo>              # from GitHub
npx ai-agent-skills install <owner/repo/skill>        # specific skill from GitHub
npx ai-agent-skills install ./path                    # from local path
npx ai-agent-skills install <name> --agent cursor     # for specific agent
npx ai-agent-skills install <name> --dry-run          # preview only

# Manage installed skills
npx ai-agent-skills uninstall <name>
npx ai-agent-skills update <name>
npx ai-agent-skills update --all

# Discovery
npx ai-agent-skills search <query>
npx ai-agent-skills info <name>

# Configuration
npx ai-agent-skills config --default-agent cursor
```

### Supported Agents

| Agent | Flag | Install Location |
|-------|------|------------------|
| Claude Code | `--agent claude` (default) | `~/.claude/skills/` |
| Cursor | `--agent cursor` | `.cursor/skills/` |
| Amp | `--agent amp` | `~/.amp/skills/` |
| VS Code / Copilot | `--agent vscode` | `.github/skills/` |
| Goose | `--agent goose` | `~/.config/goose/skills/` |
| OpenCode | `--agent opencode` | `~/.opencode/skills/` |
| Codex | `--agent codex` | `~/.codex/skills/` |
| Letta | `--agent letta` | `~/.letta/skills/` |
| Portable | `--agent project` | `.skills/` (works with any agent) |

## Manual Install

```bash
# Clone the repo
git clone https://github.com/skillcreatorai/Ai-Agent-Skills.git

# Copy a skill to your skills directory
cp -r Ai-Agent-Skills/skills/pdf ~/.claude/skills/
```

## Create Your Own


1. **Build manually**: Follow the [Agent Skills spec](https://agentskills.io/specification)

## What Are Agent Skills?

An [open standard from Anthropic](https://agentskills.io) for extending AI agents. A skill is just a folder:

```
my-skill/
├── SKILL.md       # Instructions + metadata
├── scripts/       # Optional code
└── references/    # Optional docs
```

All major AI coding tools support this format.

## Contributing

1. Fork this repo
2. Add your skill to `/skills/<name>/`
3. Ensure `SKILL.md` follows the [spec](https://agentskills.io/specification)
4. Update `skills.json`
5. Submit PR

We review all contributions for quality and spec compliance.

## Links


- [Agent Skills Spec](https://agentskills.io) - Official format documentation
- [Browse Skills](https://skillcreator.ai/explore) - Visual skill gallery with one-click install
- [Create Skills](https://skillcreator.ai/build) - Generate skills (waitlist) 
- [Anthropic Skills](https://github.com/anthropics/skills) - Official example skills

## See Also

**[openskills](https://github.com/numman-ali/openskills)** - another universal skills loader that inspired parts of this project (created pre the open agent skills standard) & Requires global install, AGENTS.md sync, and Bash calls. Great for flexibility.

**ai-agent-skills** - Just `npx`, installs to native agent folders. Homebrew for skills.

---

## Credits & Attribution

This repository builds upon and curates skills from the open-source community:

- **[Anthropic Skills](https://github.com/anthropics/skills)** - Official example skills from Anthropic that established the Agent Skills specification
- **[ComposioHQ Awesome Claude Skills](https://github.com/ComposioHQ/awesome-claude-skills)** - Curated community skills from the Composio ecosystem
- **[wshobson/agents](https://github.com/wshobson/agents)** - Development skills inspired by their plugin marketplace patterns

We believe in open source and giving credit where it's due. If you see your work here and want additional attribution, [open an issue](https://github.com/skillcreatorai/Ai-Agent-Skills/issues).

## Community

- Follow [@skillcreatorai](https://x.com/skillcreatorai) for updates
- [Open an issue](https://github.com/skillcreatorai/Ai-Agent-Skills/issues) for bugs or requests
- [Read CONTRIBUTING.md](./CONTRIBUTING.md) to add skills

---

<p align="center">
  <sub>Built with care by <a href="https://skillcreator.ai">SkillCreator.ai</a></sub>
</p>
>>>>>>> origin/feature/skill-connectivity-hub-20251226
