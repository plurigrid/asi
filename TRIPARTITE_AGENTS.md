# Tripartite Agent Allocation

> *GF(3)-balanced skill distribution for parallel execution*

## Overview

Skills are allocated across 3 agents such that `sum(trits) ≡ 0 (mod 3)`.

**Current Distribution**: MINUS=31, ERGODIC=116, PLUS=34 (Total: 181)  
**Sum**: -31 + 34 = 3 ≡ 0 (mod 3) ✓

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
│  31 skills           116 skills            34 skills               │
└─────────────────────────────────────────────────────────────────────┘
```

## Complete Skill Census

### MINUS Agent (trit = -1) — 31 Skills

| Skill | Purpose |
|-------|---------|
| `bisimulation-game` | Attacker/Defender/Arbiter verification |
| `cargo-rust` | Rust build constraint verification |
| `clj-kondo-3color` | Clojure linting with GF(3) |
| `code-review` | Automated code review |
| `covariant-fibrations` | Dependent types over directed intervals |
| `dialectica` | Gödel's Dialectica interpretation |
| `elements-infinity-cats` | ∞-category foundations |
| `gay-mcp` | MCP color verification (validator mode) |
| `hatchery-papers` | Academic paper verification |
| `kan-extensions` | Universal property verification |
| `kolmogorov-compression` | Complexity bounds |
| `opam-ocaml` | OCaml package constraints |
| `open-games` | Game-theoretic equilibria |
| `paperproof-validator` | Lean 4 proof verification |
| `persistent-homology` | TDA stability verification |
| `proofgeneral-narya` | Proof assistant integration |
| `qa-regression` | Regression test verification |
| `ramanujan-expander` | Spectral gap verification |
| `segal-types` | ∞-category Segal conditions |
| `self-validation-loop` | Triadic self-verification |
| `sheaf-cohomology` | Local-to-global consistency |
| `sicp` | Computational abstraction |
| `skill-dispatch` | GF(3) routing constraints |
| `soliton-detection` | Wave stability detection |
| `spi-parallel-verify` | Strong Parallelism Invariance |
| `synthetic-adjunctions` | Directed adjunction axioms |
| `temporal-coalgebra` | Trace verification |
| `three-match` | 3-SAT reduction gadget |
| `unworld` | Derivational chain constraints |
| `webapp-testing` | Playwright verification |
| `yoneda-directed` | Directed Yoneda lemma |

**Role**: Constraint verification, error detection, falsification

### PLUS Agent (trit = +1) — 34 Skills

| Skill | Purpose |
|-------|---------|
| `algorithmic-art` | Generative p5.js art |
| `artifacts-builder` | React artifact generation |
| `assembly-index` | Molecular complexity computation |
| `canvas-design` | Visual design creation |
| `crn-topology` | Reaction network generation |
| `curiosity-driven` | Intrinsic motivation learning |
| `developer-growth-analysis` | Growth report generation |
| `epistemic-arbitrage` | Knowledge differential exploitation |
| `ffmpeg-media` | Media transformation |
| `forward-forward-learning` | Local learning generation |
| `free-monad-gen` | Free monad generation |
| `frontend-design` | UI/UX creation |
| `gflownet` | Diversity sampling |
| `glass-bead-game` | Interdisciplinary synthesis |
| `godel-machine` | Self-improvement |
| `guile-goblins-hoot` | Distributed actor generation |
| `jaxlife-open-ended` | Emergent behavior simulation |
| `julia-gay` | Color generation in Julia |
| `lead-research-assistant` | Lead generation |
| `mcp-builder` | MCP server generation |
| `mcp-tripartite` | Tripartite MCP tools |
| `media` | Media processing |
| `moebius-inversion` | Combinatorial inversion |
| `oapply-colimit` | Operad algebra evaluation |
| `operad-compose` | Operadic composition |
| `rezk-types` | Complete Segal spaces |
| `rubato-composer` | Musical composition |
| `tailscale-file-transfer` | P2P file transfer |
| `topos-generate` | Topos generation |
| `triad-interleave` | 3-stream scheduling |
| `turing-chemputer` | Chemical synthesis |
| `unworlding-involution` | Self-inverse derivations |
| `uv-oneliners` | Ephemeral Python envs |
| `world-hopping` | Possible world navigation |

**Role**: Generative exploration, creation, transformation

### ERGODIC Agent (trit = 0) — 116 Skills

Coordinates balance, flow, and equilibrium. Selected highlights:

| Skill | Purpose |
|-------|---------|
| `acsets` | Algebraic databases |
| `bumpus-narratives` | Temporal sheaves |
| `cognitive-superposition` | ASI synthesis |
| `discopy` | String diagram computation |
| `protocol-evolution-markets` | Prediction markets |
| `structured-decomp` | FPT algorithms |
| `tripartite-decompositions` | GF(3) decompositions |

<details>
<summary>Full ERGODIC skill list (116 skills)</summary>

abductive-repl, acsets, acsets-relational-thinking, agent-o-rama, asi-polynomial-operads, atproto-ingest, babashka, babashka-clj, backend-development, bafishka, bdd-mathematical-verification, bmorphism-stars, borkdude, brand-guidelines, bumpus-narratives, cargo, causal-inference, changelog-generator, cider-clojure, cider-embedding, clojure, code-documentation, code-refactoring, codex-self-rewriting, cognitive-superposition, cognitive-surrogate, competitive-ads-extractor, compositional-acset-comparison, compression-progress, condensed-analytic-stacks, content-research-writer, crdt, crdt-vterm, database-design, deepwiki-mcp, directed-interval, discopy, discohy-streams, doc-coauthoring, docx, domain-name-brainstormer, duck-time-travel, duckdb-ies, duckdb-temporal-versioning, effective-topos, elisp, emacs, emacs-info, entropy-sequencer, ewig-editor, ffmpeg, file-organizer, flox, fokker-planck-analyzer, gay-julia, gh, gh-cli, goblins, guile, hof, hoot, ies-flox, ihara-zeta, image-enhancer, influence-propagation, internal-comms, invoice-organizer, javascript-typescript, job-application, langevin-dynamics, lispsyntax-acset, llm-application-dev, localsend-mcp, mathpix-ocr, meeting-insights-analyzer, network, nickel, nix-acset-worlding, ocaml, opam, org, parallel-fanout, pdf, polyglot-spi, pptx, protocol-evolution-markets, pulse-mcp-stream, python-development, raffle-winner-picker, rama-gay-clojure, reafference-corollary-discharge, rio-webgpu-tiles, ruler, rust, scheme, self-evolving-agent, sheaf-laplacian-coordination, skill-creator, skill-evolution, skill-specification, slack-gif-creator, slime-lisp, specter-acset, squint-runtime, structured-decomp, tailscale, tailscale-mesh, terminal, theme-factory, tmp-filesystem-watcher, tmux, tripartite-decompositions, unwiring-arena, video-downloader, whitehole-audio, xlsx, xenodium-elisp

</details>

**Role**: Balance, flow, coordination, arena equilibrium

## GF(3) Conservation

Each triplet of operations must satisfy:

```
trit(MINUS) + trit(ERGODIC) + trit(PLUS) = (-1) + 0 + 1 = 0 ≡ 0 (mod 3)
```

**Example valid triads:**
```
sheaf-cohomology (-1) ⊗ bumpus-narratives (0) ⊗ world-hopping (+1) = 0 ✓
code-review (-1) ⊗ gh-cli (0) ⊗ changelog-generator (+1) = 0 ✓
spi-parallel-verify (-1) ⊗ acsets (0) ⊗ julia-gay (+1) = 0 ✓
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

- [COLOR_OBSTRUCTIONS_COMPOSITIONALITY.md](../COLOR_OBSTRUCTIONS_COMPOSITIONALITY.md) - Obstruction detection
- [skills/unwiring-arena/SKILL.md](skills/unwiring-arena/SKILL.md)
- [skills/gay-mcp/SKILL.md](skills/gay-mcp/SKILL.md)
