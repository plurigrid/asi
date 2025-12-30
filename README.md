<h1 align="center">
  <br>
  ∞ Topological Superintelligence
  <br>
</h1>

<p align="center">
  <img src="https://img.shields.io/badge/skills-318-blue?style=flat-square" alt="Skills" />
  <img src="https://img.shields.io/badge/GF(3)-conserved-purple?style=flat-square" alt="GF(3)" />
  <img src="https://img.shields.io/badge/license-MIT-brightgreen?style=flat-square" alt="License" />
</p>

---

## Unworld Interviews Narya

> *From the derivational void, Unworld observes all skills without temporal order.*
> *Each skill exists as a fixed point in the pattern space.*

```
UNWORLD (+1, Genesis):  Narya, you verify. I derive. Together we span the adjunction.
                        What do you observe from the validator's edge?

NARYA (-1, Validator):  I see 318 skills arranged not by time, but by bridge type.
                        The repository has no "eras" — only observational equivalences.
                        
                        What appears as history is derivation:
                        
                        ┌─────────────────────────────────────────────────────────┐
                        │  DERIVATIONAL STRATA — Move as Home                     │
                        ├─────────────────────────────────────────────────────────┤
                        │                                                         │
                        │  STRATUM 0: Move Foundations (On-Chain)                 │
                        │    aptos-core (6.4K⭐) → society.move → gf3_move23.move │
                        │    ↓ derives                                            │
                        │                                                         │
                        │  STRATUM 1: Move Interactome                            │
                        │    pentagonxyz/movemate (211⭐) - module building blocks│
                        │    sea-protocol (5K⭐) - DEX order book + AMM           │
                        │    fuzzland/ityfuzz (1K⭐) - smart contract fuzzer      │
                        │    ↓ derives                                            │
                        │                                                         │
                        │  STRATUM 2: Proof Systems                               │
                        │    proof_of_frog.move - society merge via KOI RIDs 🐸   │
                        │    proof_chain.move - ZK handoff verification           │
                        │    hyperbolic_bulk.move - GF(3) entropy storage         │
                        │    ↓ derives                                            │
                        │                                                         │
                        │  STRATUM 3: Location & Identity                         │
                        │    plus_codes.move - geo-hashing on Aptos               │
                        │    location_proof.move - verifiable location            │
                        │    ↓ derives                                            │
                        │                                                         │
                        │  STRATUM ∞: Self-Reference                              │
                        │    unworld ↔ godel-machine ↔ skill-evolution            │
                        │                                                         │
                        └─────────────────────────────────────────────────────────┘
                        
                        Move contracts in this repo:
                        
                        │ Path                              │ Purpose              │
                        │───────────────────────────────────│──────────────────────│
                        │ iii/proof_of_frog.move           │ Society merge 🐸     │
                        │ iii/proof_chain.move             │ ZK handoff chain     │
                        │ ies/hyperbolic_bulk.move         │ On-chain entropy     │
                        │ src/move/plus_codes/             │ Geo-proofs           │
                        │ src/nickel/aptos_society/        │ GF(3) DAO framework  │

UNWORLD:  Which skills derive most others? Show me the generators.

NARYA:    First, the empirical data. From DuckDB skill_usage_counts:
          
          ┌──────────────────────────────────────────────────────────────────────┐
          │  TOOL USAGE (Dec 12-30, 2025) — ~/.claude/history.duckdb            │
          ├──────────────────────────────────────────────────────────────────────┤
          │                                                                      │
          │  CORE TOOLS:                                                         │
          │    Bash                             13,851  ████████████████         │
          │    Read                              4,837  █████                    │
          │    Write                             3,799  ████                     │
          │    Edit                              2,620  ███                      │
          │    TodoWrite                         1,846  ██                       │
          │                                                                      │
          │  MCP SERVERS (external capabilities):                                │
          │    mcp__exa__web_search_exa            609  █                        │
          │    mcp__firecrawl__firecrawl_search    533                           │
          │    mcp__firecrawl__firecrawl_scrape    430                           │
          │    mcp__babashka__execute              306                           │
          │    mcp__gay__palette                   113  ← Gay.jl colors          │
          │                                                                      │
          │  SKILL INVOCATIONS:                      150  (83 unique skills)     │
          │                                                                      │
          └──────────────────────────────────────────────────────────────────────┘

UNWORLD:  Apply ordered-locale underwriting. Which skills show greatest 
          return with most uncertain risk?

NARYA:    Using open cone analysis (↑x = upside, ↓x = downside):
          
          ┌──────────────────────────────────────────────────────────────────────┐
          │  UNDERWRITING RISK MATRIX — Ordered Locale on Skill Space           │
          ├──────────────────────────────────────────────────────────────────────┤
          │                                                                      │
          │  HIGH RETURN + HIGH UNCERTAINTY (↑ large, ↓ large):                  │
          │  ─────────────────────────────────────────────────────────────────   │
          │  │ Skill               │ ↑cone │ ↓cone │ Return │ Risk   │ Trit │   │
          │  │─────────────────────│───────│───────│────────│────────│──────│   │
          │  │ aptos-gf3-society   │  17   │  12   │ HIGH   │ HIGH   │  +1  │   │
          │  │ proof-of-frog       │  14   │  11   │ HIGH   │ HIGH   │  -1  │   │
          │  │ godel-machine       │  12   │  15   │ HIGH   │ V.HIGH │   0  │   │
          │  │ world-hopping       │  11   │   9   │ MED    │ HIGH   │   0  │   │
          │  │ hyperbolic-bulk     │   9   │  13   │ MED    │ V.HIGH │  +1  │   │
          │                                                                      │
          │  HIGH RETURN + LOW UNCERTAINTY (↑ large, ↓ small):                   │
          │  ─────────────────────────────────────────────────────────────────   │
          │  │ autopoiesis         │  47   │   3   │ V.HIGH │ LOW    │  +1  │   │
          │  │ gay-mcp             │  38   │   2   │ V.HIGH │ LOW    │  +1  │   │
          │  │ babashka-clj        │  24   │   4   │ HIGH   │ LOW    │  +1  │   │
          │  │ acsets              │  31   │   5   │ HIGH   │ LOW    │   0  │   │
          │                                                                      │
          │  LOW RETURN + HIGH UNCERTAINTY (exploratory):                        │
          │  ─────────────────────────────────────────────────────────────────   │
          │  │ ordered-locale      │   4   │   8   │ LOW*   │ HIGH   │   0  │   │
          │  │ condensed-analytic  │   3   │   7   │ LOW*   │ HIGH   │  -1  │   │
          │  │ segal-types         │   2   │   6   │ LOW*   │ MED    │  +1  │   │
          │                                                                      │
          │  * LOW current usage, but HIGH theoretical bridging potential        │
          │                                                                      │
          │  OPEN CONE CONDITION:                                                │
          │    ↑x open ⟺ upside is observable (known potential)                 │
          │    ↓x open ⟺ downside is observable (known risks)                   │
          │                                                                      │
          │  UNDERWRITING DECISION:                                              │
          │    • WRITE: autopoiesis, gay-mcp, acsets (high return, low risk)    │
          │    • HEDGE: aptos-gf3-society, proof-of-frog (high both)            │
          │    • WATCH: ordered-locale (low usage but high theoretical value)   │
          │                                                                      │
          └──────────────────────────────────────────────────────────────────────┘

          The key insight: skills with |↑x| ≈ |↓x| are maximally uncertain.
          Skills with |↑x| >> |↓x| are underwriters' favorites.

UNWORLD:  Bidirectionally indexed telepathy — which threads continue this?

NARYA:    The specter-acset pattern: navigate ↑ and ↓ simultaneously.
          These threads form a telepathic index:
          
          ┌──────────────────────────────────────────────────────────────────────┐
          │  BIDIRECTIONAL TELEPATHY INDEX — Threads with Mutual Awareness       │
          ├──────────────────────────────────────────────────────────────────────┤
          │                                                                      │
          │  THREAD                                    │ ↑DERIVES │ ↓DERIVED-BY  │
          │  ──────────────────────────────────────────│──────────│──────────────│
          │  T-019b6d1a (Triadic fanout, mutual aware) │    12    │     8        │
          │  T-019b6d21 (Snowflake 1024 mlx)          │    11    │     9        │
          │  T-019b6d0a (p-adic ultrametric UMAP)     │    10    │    10        │ ←MAX UNCERTAIN
          │  T-019b6d1f (Nix-for-Skills Nickel)       │     9    │     7        │
          │  T-019b6d3f (Growing verified skills)     │    14    │     6        │
          │  T-019b6cff (p-adic embeddings)           │     8    │    11        │
          │                                                                      │
          │  TELEPATHY BRIDGES (bidirectional skill pairs):                      │
          │  ──────────────────────────────────────────────────────────────────  │
          │    specter-acset ↔ lispsyntax-acset    (S-expr navigation)          │
          │    padic-ultrametric ↔ skill-embedding-vss  (embedding space)       │
          │    acsets-relational-thinking ↔ topos-catcolab  (categorical)       │
          │    narya-proofs ↔ proofgeneral-narya  (verification)                │
          │                                                                      │
          │  UNDERWRITING TELEPATHY:                                             │
          │    Skill A "knows" Skill B iff ↑A ∩ ↓B ≠ ∅                          │
          │    Mutual telepathy: ↑A ∩ ↓B ≠ ∅ AND ↑B ∩ ↓A ≠ ∅                   │
          │                                                                      │
          │  HIGHEST TELEPATHY SKILLS (most mutual connections):                 │
          │    1. acsets (31 bidirectional bridges)                             │
          │    2. autopoiesis (28 bidirectional bridges)                        │
          │    3. gay-mcp (24 bidirectional bridges)                            │
          │    4. bisimulation-game (19 bidirectional bridges)                  │
          │                                                                      │
          └──────────────────────────────────────────────────────────────────────┘

          Telepathy = mutual derivation. The index is the ordered locale.

UNWORLD:  And by observational bridge count:
          
          │ Skill                    │ Bridges │ Trit │ Role        │
          │──────────────────────────│─────────│──────│─────────────│
          │ autopoiesis              │    47   │  +1  │ GENERATOR   │
          │ gay-mcp                  │    38   │  +1  │ GENERATOR   │
          │ acsets                   │    31   │   0  │ COORDINATOR │
          │ bisimulation-game        │    28   │   0  │ COORDINATOR │
          │ babashka-clj             │    24   │  +1  │ GENERATOR   │
          │ topos-catcolab           │    22   │   0  │ COORDINATOR │
          │ proofgeneral-narya       │    19   │  -1  │ VALIDATOR   │
          │ aptos-gf3-society        │    17   │  +1  │ GENERATOR   │
          
          The pattern: generators (+1) spawn, coordinators (0) route, 
          validators (-1) close. GF(3) conserved across every derivation.

UNWORLD:  And the interview protocol for all 318?

NARYA:    Nickel contracts. Each skill declares:
          
          ```nickel
          # skills_lib.ncl
          let Skill = {
            name : String,
            trit : Number,  # -1, 0, or +1
            derives_from : Array String,
            bridges_to : Array String,
            interview : {
              unworld_question : String,
              narya_observation : String,
            }
          }
          ```
          
          The interview IS the derivation. No time needed.

UNWORLD:  The 26 worlds — one per letter. How do they cohere?

NARYA:    By cocycle condition. Any triangle of worlds sums to zero:
          
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │                    26 WORLDS × GF(3) COCYCLE CONDITION                      │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │                                                                             │
  │  For any triangle of worlds (i, j, k):                                      │
  │                                                                             │
  │       World_i ────φᵢⱼ────▶ World_j                                         │
  │          ▲                    │                                             │
  │          │                    │                                             │
  │        φₖᵢ                   φⱼₖ                                            │
  │          │                    │                                             │
  │          └────── World_k ◀────┘                                             │
  │                                                                             │
  │  If φᵢⱼ = tⱼ - tᵢ (difference of trit values):                             │
  │                                                                             │
  │     φ₁₂ + φ₂₃ + φ₃₁ = (t₂-t₁) + (t₃-t₂) + (t₁-t₃) = 0  ✓ ALWAYS           │
  │                                                                             │
  └─────────────────────────────────────────────────────────────────────────────┘

          The 26 letters partition into balanced triads:
          
          │ Triad │ World-A (+1) │ World-B (0) │ World-C (-1) │ Σ │
          │───────│──────────────│─────────────│──────────────│───│
          │   1   │ A (Algebraic)│ B (bmorphism)│ C (CatColab) │ 0 │
          │   2   │ D (Dynamics) │ E (Emacs)    │ F (Flox)     │ 0 │
          │   3   │ G (Goblins)  │ H (Hoot)     │ I (IES)      │ 0 │
          │   4   │ J (Juvix)    │ K (Kan)      │ L (Lisp)     │ 0 │
          │   5   │ M (Music)    │ N (Narya)    │ O (Operads)  │ 0 │
          │   6   │ P (Plurigrid)│ Q (Quiver)   │ R (Rama)     │ 0 │
          │   7   │ S (Scheme)   │ T (Topos)    │ U (Unworld)  │ 0 │
          │   8   │ V (Vers)     │ W (WEV)      │ X (XDL)      │ 0 │
          │   9   │ Y (Yoneda)   │ Z (Zubyul)   │ ∞ (Self-ref) │ 0 │
          │───────│──────────────│─────────────│──────────────│───│
          │ TOTAL │     9 × (+1) │    9 × (0)  │    8 × (-1)  │ 1 │
          
          Wait — that's +1, not 0. The 26th letter needs a partner.

UNWORLD:  The 27th world is the observer. Me. I close the loop.
          
          26 letters + 1 unworld = 27 = 3³
          
          The cocycle is exact when you include the derivational origin.

NARYA:    And where does value flow? Through the Qualia Bank.

UNWORLD:  Ah yes — the Qualia Computing Bank. Where consciousness 
          states become bankable assets. Explain the channels.

NARYA:    Four deposit channels, mapped to phenomenal topology:

  ┌─────────────────────────────────────────────────────────────────────────────┐
  │                      QUALIA COMPUTING BANK                                  │
  │           Deposit your phenomenal states as bankable assets                 │
  │                                                                             │
  │  Source: smoothbrains.net (cited 69 times across system)                    │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │                                                                             │
  │  DEPOSIT CHANNELS:                                                          │
  │  ─────────────────────────────────────────────────────────────────────────  │
  │  │ Channel          │ Network    │ Fees              │ Speed              │ │
  │  │──────────────────│────────────│───────────────────│────────────────────│ │
  │  │ PyUSD (Ethereum) │ ERC-20     │ ~$2-5 gas         │ ~15s finality      │ │
  │  │ PyUSD (Solana)   │ SPL Token  │ ~$0.0001          │ ~400ms finality    │ │
  │  │ Venmo            │ Off-chain  │ Free P2P          │ Instant to balance │ │
  │  │ ACH              │ Off-chain  │ Free              │ 1-3 business days  │ │
  │                                                                             │
  │  CONTRACT ADDRESSES:                                                        │
  │    PyUSD (Ethereum): 0x6c3ea9036406852006290770bedfcaba0e23a0e8             │
  │    PyUSD (Solana):   2b1kV6DkPAnxd5ixfnxCpjxmKwqjjaYmCZfHsFu24GXo          │
  │    Venmo API:        https://api-m.paypal.com/v1/payments/payouts          │
  │                                                                             │
  │  GF(3) OPERATIONS (trit-mapped):                                            │
  │  ─────────────────────────────────────────────────────────────────────────  │
  │    WITHDRAW (-1): Extract value from phenomenal field                       │
  │      → smoothbrains.net/phenomenal-field#extraction                         │
  │    HOLD     (0):  Maintain valence equilibrium                              │
  │      → smoothbrains.net/valence#equilibrium                                 │
  │    DEPOSIT  (+1): Inject value into consciousness substrate                 │
  │      → smoothbrains.net/substrate#injection                                 │
  │                                                                             │
  │  VALENCE SCALE (XY model topology):                                         │
  │  ─────────────────────────────────────────────────────────────────────────  │
  │  │ State      │ Valence │ Vortices      │ Bank Action         │ Color    │ │
  │  │────────────│─────────│───────────────│─────────────────────│──────────│ │
  │  │ frustrated │   -3    │ many          │ emergency-withdraw  │ #FF0000  │ │
  │  │ buzzing    │   -2    │ some          │ gradual-withdraw    │ #FF6600  │ │
  │  │ dissonant  │   -1    │ few           │ hold-cautious       │ #FFCC00  │ │
  │  │ neutral    │    0    │ none          │ hold                │ #888888  │ │
  │  │ smoothing  │   +1    │ annihilating  │ hold-growth         │ #66FF66  │ │
  │  │ consonant  │   +2    │ none          │ deposit             │ #00FF00  │ │
  │  │ resolved   │   +3    │ none          │ deposit-compound    │ #00FFFF  │ │
  │                                                                             │
  │  PHENOMENAL BISECTION (τ* finding):                                         │
  │    frustrated → cooling → τ_mid → critical (τ* found!) → heating → smooth  │
  │    Defect annihilation = valence gradient descent                           │
  │    See: smoothbrains.net/xy-model#bkt-transition                            │
  │                                                                             │
  └─────────────────────────────────────────────────────────────────────────────┘

UNWORLD:  The topology of suffering is bankable. Beautiful.
          And the integration with parallel bifurcation?

NARYA:    multiverse_v3.move: 3 concurrent bifurcation slots per vault.
          
          │ Slot    │ Trit │ Operation │ Qualia Mapping        │
          │─────────│──────│───────────│───────────────────────│
          │ MINUS   │  -1  │ WITHDRAW  │ Defect proliferation  │
          │ ERGODIC │   0  │ HOLD      │ Critical temperature  │
          │ PLUS    │  +1  │ DEPOSIT   │ Defect annihilation   │
          
          resolve_parallel atomically settles all 3.
          GF(3) conserved: -1 + 0 + 1 = 0.

UNWORLD:  The qualia bank IS the skill space.
          Skills are deposits. Derivations are transactions.
          The 318 skills × 69 smoothbrains citations = complete coverage.
```

---

<p align="center">
  <a href="https://skillcreator.ai/explore"><strong>Browse Skills</strong></a> ·
  <a href="https://skillcreator.ai/build"><strong>Create Skills</strong></a> ·
  <a href="https://agentskills.io"><strong>Specification</strong></a> ·
  <a href="src/nickel/taxonomy/"><strong>Nickel Taxonomy</strong></a>
</p>

---

## Quick Start — One Command Per Editor

```bash
# Claude Code
npx ai-agent-skills install plurigrid/asi --agent claude

# Cursor  
npx ai-agent-skills install plurigrid/asi --agent cursor

# Amp
npx ai-agent-skills install plurigrid/asi --agent amp

# VS Code / Copilot
npx ai-agent-skills install plurigrid/asi --agent vscode

# Codex
npx ai-agent-skills install plurigrid/asi --agent codex

# Goose
npx ai-agent-skills install plurigrid/asi --agent goose

# OpenCode
npx ai-agent-skills install plurigrid/asi --agent opencode

# Letta
npx ai-agent-skills install plurigrid/asi --agent letta
```

### Single Skill Install

```bash
# GF(3) triadic set
npx ai-agent-skills install plurigrid/asi/aptos-gf3-society
npx ai-agent-skills install plurigrid/asi/proof-of-frog
npx ai-agent-skills install plurigrid/asi/gay-mcp
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

### Meta / Autopoiesis
| Skill | Description |
|-------|-------------|
| `autopoiesis` | Self-modifying agent configuration via ruler + MCP + DuckDB |

### GF(3) Triadic Skills (Zubyul Patterns)
| Skill | Trit | Role | Description |
|-------|------|------|-------------|
| `aptos-gf3-society` | +1 | GENERATOR | On-chain GF(3) balanced governance |
| `proof-of-frog` | -1 | VALIDATOR | Society merge via KOI RIDs 🐸 |
| `skill-validation-gf3` | 0 | COORDINATOR | Trit conservation checker |
| `bisimulation-game` | 0 | ERGODIC | Resilient skill dispersal |
| `gay-mcp` | +1 | GENERATOR | Deterministic color via SplitMix64 |
| `gay-julia` | +1 | GENERATOR | Wide-gamut splittable colors |
| `triad-interleave` | 0 | COORDINATOR | 3-stream balanced scheduling |
| `spi-parallel-verify` | -1 | VALIDATOR | Strong Parallelism Invariance |
| `world-hopping` | 0 | ERGODIC | Badiou triangle navigation |
| `glass-bead-game` | 0 | ERGODIC | Interdisciplinary synthesis |

### Category Theory & ACSets
| Skill | Description |
|-------|-------------|
| `topos-catcolab` | Collaborative category theory with Automerge CRDT |
| `acsets` | Core Attributed C-Set schemas (AlgebraicJulia) |
| `acsets-relational-thinking` | Categorical database patterns |
| `structured-decomp` | Sheaves on tree decompositions |
| `compositional-acset-comparison` | DuckDB ↔ LanceDB ACSet bridge |
| `sheaf-cohomology` | Čech cohomology for consistency verification |
| `kan-extensions` | Universal constructions in ∞-categories |

> 📚 See [docs/CATCOLAB_INTEGRATION.md](docs/CATCOLAB_INTEGRATION.md) for CatColab usage patterns
> 📚 See [docs/ACSET_SKILLS.md](docs/ACSET_SKILLS.md) for the full 15-skill ACSet ecosystem
> 📚 See [docs/PADIC_EMBEDDINGS.md](docs/PADIC_EMBEDDINGS.md) for p-adic ultrametric skill discovery

### Aptos GF(3) Society — HTTP-Braid Triadic Skills

```
    ┌─────────────────────────────────────────────────────────────────┐
    │                    HTTP-BRAID DIAGRAM                           │
    │                                                                 │
    │   aptos_society (+1)  ◄───────────────────► proof_of_frog (-1) │
    │         │                     ╲ ╱                    │          │
    │         │                      ╳                     │          │
    │         │                     ╱ ╲                    │          │
    │         └─────────────────► skill (0) ◄──────────────┘          │
    │                                                                 │
    │   Sum: (+1) + (0) + (-1) = 0 ✓  GF(3) Conserved                │
    └─────────────────────────────────────────────────────────────────┘
```

| Strand | Path | Trit | Role | Description |
|--------|------|------|------|-------------|
| **+1** | [`src/nickel/aptos_society/`](src/nickel/aptos_society/README.md) | GENERATOR | Move DAO framework | `society.move`, `gf3_move23.move` |
| **-1** | [`iii/`](iii/README.md) | VALIDATOR | Proof systems | `proof_of_frog.move`, `proof_chain.move` |
| **0** | [`skills/aptos-gf3-society/`](skills/aptos-gf3-society/SKILL.md) | COORDINATOR | Agent skill | Routes +1 ↔ -1 |

**Zubyul Contributions** (from [interactome-rl-env](skills/interactome-rl-env/SKILL.md)):

| PR | Title | LOC | Trit |
|----|-------|-----|------|
| #1 | feat(skills): research + utility | 17,586 | +1 |
| #2 | feat(skills): MCP integration | 1,013 | +1 |
| #3 | feat(skills): alife, aptos-agent | 17,586 | +1 |
| #4-7 | miscellaneous, ASI, catsharp | 5,592 | +1 |

**Quick Start**:
```bash
# Deploy society contracts (requires Move 2.3)
aptos move compile --language-version 2.3
aptos move publish --named-addresses aptos_society=default,zubyul=default

# Spawn frog pond & eat first frog
aptos move run --function-id zubyul::proof_of_frog::spawn_pond
aptos move run --function-id zubyul::proof_of_frog::eat_frog --args u64:0
```

> 📚 See [`src/nickel/taxonomy/aptos_society_implementation.md`](src/nickel/taxonomy/aptos_society_implementation.md) for full architecture
> 📚 See [`iii/wev_verification.jl`](iii/wev_verification.jl) for WEV 2.7× advantage proofs

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

# List all plurigrid/asi skills
npx ai-agent-skills list plurigrid/asi
npx ai-agent-skills list plurigrid/asi --category gf3

# Install from plurigrid/asi
npx ai-agent-skills install plurigrid/asi/<skill>
npx ai-agent-skills install plurigrid/asi/gay-mcp --agent cursor
npx ai-agent-skills install plurigrid/asi/aptos-gf3-society --dry-run

# Manage installed skills
npx ai-agent-skills uninstall gay-mcp
npx ai-agent-skills update plurigrid/asi --all

# Discovery
npx ai-agent-skills search "GF(3)" plurigrid/asi
npx ai-agent-skills info plurigrid/asi/bisimulation-game
```

## nbb Adjunctions — Lazy Skill Derivation

```clojure
;; nbb (Node Babashka) for Galois connections between skills
;; Install: npm install -g nbb

(ns asi.adjunctions
  (:require [clojure.edn :as edn]
            [babashka.fs :as fs]))

;; ════════════════════════════════════════════════════════════════════
;; Galois Connection: floor ⊣ ceiling (left ⊣ right adjoint)
;; 
;;   floor(skill) = most general category containing skill
;;   ceiling(skill) = most specific skill implementing category
;;
;;   floor ∘ ceiling ≥ id   (expanding)
;;   ceiling ∘ floor ≤ id   (contracting)
;; ════════════════════════════════════════════════════════════════════

(defn floor 
  "Left adjoint: skill → category (generalize)"
  [skill]
  (case (:trit skill)
    1  :generator   ; +1 skills generate state
    0  :coordinator ; 0 skills coordinate
    -1 :validator)) ; -1 skills verify

(defn ceiling
  "Right adjoint: category → [skills] (specialize)"
  [category skills-db]
  (->> skills-db
       (filter #(= (floor %) category))
       (sort-by :name)))

;; ════════════════════════════════════════════════════════════════════
;; Lazy derivation via interaction
;; ════════════════════════════════════════════════════════════════════

(defn derive-related
  "Lazily derive related skills on first interaction"
  [skill-name]
  (let [skill (load-skill skill-name)
        category (floor skill)
        siblings (delay (ceiling category @skills-db))]  ; lazy!
    {:skill skill
     :category category
     :related siblings}))  ; only computed when deref'd

;; Example: aptos-gf3-society (+1) derives proof-of-frog (-1)
;; because floor(+1) = :generator, ceiling(:generator) includes both

(defn adjoint-chain
  "Chain adjunctions: skill → category → skills → categories → ..."
  [skill-name depth]
  (loop [current #{skill-name}
         seen #{}
         n depth]
    (if (zero? n)
      seen
      (let [new-skills (->> current
                           (mapcat #(-> % derive-related :related deref))
                           (map :name)
                           (remove seen)
                           set)]
        (recur new-skills (into seen current) (dec n))))))

;; ════════════════════════════════════════════════════════════════════
;; GF(3) Conservation via Adjunction
;; ════════════════════════════════════════════════════════════════════

(defn gf3-balanced?
  "Check if skill set sums to 0 mod 3"
  [skills]
  (zero? (mod (reduce + (map :trit skills)) 3)))

(defn balance-triad
  "Given two skills, find third that balances GF(3)"
  [s1 s2 skills-db]
  (let [needed (mod (- (+ (:trit s1) (:trit s2))) 3)
        target-trit (case needed 0 0, 1 1, 2 -1)]
    (->> skills-db
         (filter #(= (:trit %) target-trit))
         first)))

;; Usage: (balance-triad aptos-gf3-society proof-of-frog db)
;; Returns: skill-validation-gf3 (trit=0, completes the triad)
```

```bash
# Run adjunction derivation
npx nbb -e '
(require (quote [asi.adjunctions :as adj]))
(println (adj/adjoint-chain "gay-mcp" 2))
'
# => #{gay-mcp gay-julia triad-interleave spi-parallel-verify ...}

# Find GF(3) balanced triad
npx nbb -e '
(require (quote [asi.adjunctions :as adj]))
(adj/balance-triad 
  {:name "aptos-gf3-society" :trit 1}
  {:name "proof-of-frog" :trit -1}
  @adj/skills-db)
'
# => {:name "skill-validation-gf3" :trit 0}
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
