# Synergistic 3-Tuples: Skill Loading with GF(3) Conservation

## Overview

Skills are loaded via symlinks from `.ruler/skills/` to `.agents/skills/`. Each skill has a **trit assignment** (-1, 0, +1) that enables **GF(3) conservation** when skills are combined in triads.

## Autopoiesis: Self-Rewriting ACSet

The system supports **self-modification** via `bin/autopoi.bb`:

```bash
just autopoi-init           # Initialize autopoiesis database
just autopoi-skill name trit # Add skill to all agents
just autopoi-system name seed trit  # Register an agent system
just autopoi-verify         # Check operational closure
```

**Key insight:** DPO rewriting ensures `produces ∘ regenerates = id_System` — components regenerate the system that produced them, creating operational closure.

See: [autopoiesis skill](.agents/skills/autopoiesis/SKILL.md), [thread T-019b5197](https://ampcode.com/threads/T-019b5197-5e59-778a-b515-a2a84df7e644)

## Trit Polarity → Subagent Role

| Trit | Polarity | Color | Subagent | Action |
|------|----------|-------|----------|--------|
| -1 | MINUS | Blue (#2626D8) | **Validator** | Verify, constrain, reduce |
| 0 | ERGODIC | Green (#26D826) | **Coordinator** | Transport, derive, navigate |
| +1 | PLUS | Red (#D82626) | **Generator** | Create, compose, generate |

## Canonical Triads (GF(3) = 0)

Each triad sums to 0 mod 3, ensuring conservation:

```
# Core Bundles
three-match (-1) ⊗ unworld (0) ⊗ gay-mcp (+1) = 0 ✓  [Core System]
slime-lisp (-1) ⊗ borkdude (0) ⊗ cider-clojure (+1) = 0 ✓  [REPL]
clj-kondo-3color (-1) ⊗ acsets (0) ⊗ rama-gay-clojure (+1) = 0 ✓  [Database]
hatchery-papers (-1) ⊗ mathpix-ocr (0) ⊗ bmorphism-stars (+1) = 0 ✓  [Research]
proofgeneral-narya (-1) ⊗ squint-runtime (0) ⊗ gay-mcp (+1) = 0 ✓  [Runtime]

# Cohomological Bundle (NEW 2025-12-21)
sheaf-cohomology (-1) ⊗ kan-extensions (0) ⊗ free-monad-gen (+1) = 0 ✓  [Schema]
temporal-coalgebra (-1) ⊗ dialectica (0) ⊗ operad-compose (+1) = 0 ✓  [Game]
persistent-homology (-1) ⊗ open-games (0) ⊗ topos-generate (+1) = 0 ✓  [Topos]

# DiscoHy Operad Bundle (NEW 2025-12-22)
cubes (-1) ⊗ discohy-streams (0) ⊗ little-disks (+1) = 0 ✓  [E_n Operads]
cactus (-1) ⊗ thread (0) ⊗ modular (+1) = 0 ✓  [Thread Operads]
gravity (-1) ⊗ thread (0) ⊗ swiss-cheese (+1) = 0 ✓  [Dynamical]
three-match (-1) ⊗ acsets (0) ⊗ libkind-directed (+1) = 0 ✓  [Libkind-Spivak]

# ACSets Triangulated Bundle (NEW 2025-12-22, from 3-agent triangulation)
bumpus-width (-1) ⊗ acsets (0) ⊗ libkind-directed (+1) = 0 ✓  [FPT Algorithms]
schema-validation (-1) ⊗ acsets (0) ⊗ oapply-colimit (+1) = 0 ✓  [Composition]
temporal-coalgebra (-1) ⊗ acsets (0) ⊗ koopman-generator (+1) = 0 ✓  [Dynamics]

# Unified Time-Varying Data Bundle (NEW 2025-12-22, from Brunton+Spivak+Schultz)
dmd-spectral (-1) ⊗ structured-decomp (0) ⊗ koopman-generator (+1) = 0 ✓  [Decomposition]
sheaf-cohomology (-1) ⊗ structured-decomp (0) ⊗ colimit-reconstruct (+1) = 0 ✓  [Reconstruction]
interval-presheaf (-1) ⊗ algebraic-dynamics (0) ⊗ oapply-colimit (+1) = 0 ✓  [Composition]

# ASI Polynomial Operads Bundle (NEW 2025-12-22, from Spivak+Libkind+Bumpus+Hedges)
cohomology-obstruction (-1) ⊗ asi-polynomial-operads (0) ⊗ pattern-runs-on-matter (+1) = 0 ✓  [Module Action]
spined-categories (-1) ⊗ asi-polynomial-operads (0) ⊗ open-games-arena (+1) = 0 ✓  [Decomposition]
bumpus-width (-1) ⊗ asi-polynomial-operads (0) ⊗ free-monad-trees (+1) = 0 ✓  [Complexity]

# LHoTT Cohesive Linear Bundle (NEW 2025-12-22, from Schreiber+Corfield)
persistent-homology (-1) ⊗ lhott-cohesive-linear (0) ⊗ topos-generate (+1) = 0 ✓  [Tangent ∞-Topos]
sheaf-cohomology (-1) ⊗ lhott-cohesive-linear (0) ⊗ gay-mcp (+1) = 0 ✓  [Cohesive Color]
proofgeneral-narya (-1) ⊗ lhott-cohesive-linear (0) ⊗ rubato-composer (+1) = 0 ✓  [Linear Music]
three-match (-1) ⊗ lhott-cohesive-linear (0) ⊗ gay-mcp (+1) = 0 ✓  [Interaction Entropy]

# Condensed Analytic Stacks Bundle (NEW 2025-12-22, from Scholze+Clausen+Kesting)
sheaf-cohomology (-1) ⊗ condensed-analytic-stacks (0) ⊗ gay-mcp (+1) = 0 ✓  [Liquid Color]
persistent-homology (-1) ⊗ condensed-analytic-stacks (0) ⊗ topos-generate (+1) = 0 ✓  [Solid Topos]
proofgeneral-narya (-1) ⊗ condensed-analytic-stacks (0) ⊗ rubato-composer (+1) = 0 ✓  [Pyknotic Music]
temporal-coalgebra (-1) ⊗ condensed-analytic-stacks (0) ⊗ operad-compose (+1) = 0 ✓  [6-Functor]

# Cognitive Surrogate Bundle (NEW 2025-12-22, from plurigrid/asi Layers 4-7)
influence-propagation (-1) ⊗ cognitive-surrogate (0) ⊗ agent-o-rama (+1) = 0 ✓  [Layer 6-7 Fidelity]
polyglot-spi (-1) ⊗ entropy-sequencer (0) ⊗ pulse-mcp-stream (+1) = 0 ✓  [Layer 1-5 Pipeline]
influence-propagation (-1) ⊗ abductive-repl (0) ⊗ gay-mcp (+1) = 0 ✓  [Abductive Inference]
polyglot-spi (-1) ⊗ cognitive-surrogate (0) ⊗ agent-o-rama (+1) = 0 ✓  [Cross-Language Learning]

# LispSyntax ACSet Bundle (NEW 2025-12-22, from OCaml ppx_sexp_conv pattern)
slime-lisp (-1) ⊗ lispsyntax-acset (0) ⊗ cider-clojure (+1) = 0 ✓  [Sexp Serialization]
three-match (-1) ⊗ lispsyntax-acset (0) ⊗ gay-mcp (+1) = 0 ✓  [Colored Sexp]
polyglot-spi (-1) ⊗ lispsyntax-acset (0) ⊗ geiser-chicken (+1) = 0 ✓  [Scheme Bridge]

# Cognitive Superposition Bundle (NEW 2025-12-22, from Riehl+Sutskever+Schmidhuber+Bengio)
segal-types (-1) ⊗ cognitive-superposition (0) ⊗ gflownet (+1) = 0 ✓  [Riehl-Bengio]
yoneda-directed (-1) ⊗ cognitive-superposition (0) ⊗ curiosity-driven (+1) = 0 ✓  [Riehl-Schmidhuber]
kolmogorov-compression (-1) ⊗ cognitive-superposition (0) ⊗ godel-machine (+1) = 0 ✓  [Sutskever-Schmidhuber]
sheaf-cohomology (-1) ⊗ causal-inference (0) ⊗ gflownet (+1) = 0 ✓  [Categorical-Bengio]
persistent-homology (-1) ⊗ causal-inference (0) ⊗ self-evolving-agent (+1) = 0 ✓  [Topological-Schmidhuber]
proofgeneral-narya (-1) ⊗ causal-inference (0) ⊗ forward-forward-learning (+1) = 0 ✓  [Proof-Hinton]

# Synthetic ∞-Category Bundle (NEW 2025-12-22, from Riehl-Shulman)
segal-types (-1) ⊗ directed-interval (0) ⊗ rezk-types (+1) = 0 ✓  [Core ∞-Cats]
covariant-fibrations (-1) ⊗ directed-interval (0) ⊗ synthetic-adjunctions (+1) = 0 ✓  [Transport]
yoneda-directed (-1) ⊗ elements-infinity-cats (0) ⊗ synthetic-adjunctions (+1) = 0 ✓  [Yoneda-Adjunction]

# Assembly Theory Bundle (NEW 2025-12-22, from Cronin Chemputer)
assembly-index (-1) ⊗ turing-chemputer (0) ⊗ crn-topology (+1) = 0 ✓  [Molecular Complexity]
kolmogorov-compression (-1) ⊗ turing-chemputer (0) ⊗ dna-origami (+1) = 0 ✓  [Self-Assembly]

# Specter Navigation Bundle (NEW 2025-12-22, Correct-by-Construction Caching)
# Key insight: 3-MATCH local constraints → global cache correctness
# Tuple paths enable type-stable inline caching with 0 allocations
three-match (-1) ⊗ lispsyntax-acset (0) ⊗ gay-mcp (+1) = 0 ✓  [Path Validation]
polyglot-spi (-1) ⊗ lispsyntax-acset (0) ⊗ gay-mcp (+1) = 0 ✓  [Cross-Lang Navigation]
sheaf-cohomology (-1) ⊗ acsets (0) ⊗ gay-mcp (+1) = 0 ✓  [ACSet Navigation]

# DeepWiki Research Bundle (NEW 2025-12-22, Repository Documentation via MCP)
# Free, no-auth access to AI-generated docs for any public GitHub repo
hatchery-papers (-1) ⊗ deepwiki-mcp (0) ⊗ bmorphism-stars (+1) = 0 ✓  [Research]
persistent-homology (-1) ⊗ deepwiki-mcp (0) ⊗ gay-mcp (+1) = 0 ✓  [Documentation]
sheaf-cohomology (-1) ⊗ deepwiki-mcp (0) ⊗ topos-generate (+1) = 0 ✓  [Knowledge]
three-match (-1) ⊗ deepwiki-mcp (0) ⊗ cider-clojure (+1) = 0 ✓  [Clojure Repos]
polyglot-spi (-1) ⊗ deepwiki-mcp (0) ⊗ gay-mcp (+1) = 0 ✓  [Cross-Lang Docs]

# Ramanujan Spectral Bundle (NEW 2025-12-22, Edge Growth + Möbius Centrality)
# Key insight: Alon-Boppana λ₂ ≥ 2√(d-1) is unbreakable
# Non-backtracking walks encode prime cycles via Ihara zeta
# Möbius inversion harmonizes centrality validity predicates
ramanujan-expander (-1) ⊗ ihara-zeta (0) ⊗ moebius-inversion (+1) = 0 ✓  [Spectral Core]
ramanujan-expander (-1) ⊗ acsets (0) ⊗ gay-mcp (+1) = 0 ✓  [Graph Coloring]
ramanujan-expander (-1) ⊗ acsets (0) ⊗ moebius-inversion (+1) = 0 ✓  [Edge Growth]
ramanujan-expander (-1) ⊗ influence-propagation (0) ⊗ agent-o-rama (+1) = 0 ✓  [Centrality]
ihara-zeta (-1) ⊗ acsets (0) ⊗ moebius-inversion (+1) = 0 ✓  [Prime Cycles]
three-match (-1) ⊗ ihara-zeta (0) ⊗ moebius-inversion (+1) = 0 ✓  [Chromatic Polynomial]

# Compositional ACSet Comparison Bundle (NEW 2025-12-22, DuckDB vs LanceDB via ACSets)
# Key insight: Golden thread φ-angle walk (137.508°) for maximal dimension dispersion
# Lance SDK 1.0.0 milestone: SemVer for SDK, independent versioning for formats
# Homoiconic: algorithm ↔ data boundary dissolves in self-hosted Lisps
# Phase-scoped evaluation avoids unintentional entanglement
schema-validation (-1) ⊗ compositional-acset-comparison (0) ⊗ gay-mcp (+1) = 0 ✓  [Property Analysis]
three-match (-1) ⊗ compositional-acset-comparison (0) ⊗ koopman-generator (+1) = 0 ✓  [Dynamic Traversal]
temporal-coalgebra (-1) ⊗ compositional-acset-comparison (0) ⊗ oapply-colimit (+1) = 0 ✓  [Versioning]
polyglot-spi (-1) ⊗ compositional-acset-comparison (0) ⊗ gay-mcp (+1) = 0 ✓  [Homoiconic Interop]

# IES Environment Bundle (NEW 2025-12-22, FloxHub bmorphism/ies)
# Flox environment composition with DuckDB social analysis
# Gay.jl/Gay.bb deterministic coloring integration
polyglot-spi (-1) ⊗ ies (0) ⊗ gay-mcp (+1) = 0 ✓  [Environment]
three-match (-1) ⊗ ies (0) ⊗ pulse-mcp-stream (+1) = 0 ✓  [Social Analysis]
influence-propagation (-1) ⊗ ies (0) ⊗ agent-o-rama (+1) = 0 ✓  [Cognitive Surrogate]
temporal-coalgebra (-1) ⊗ ies (0) ⊗ cider-clojure (+1) = 0 ✓  [Clojure/Julia Bridge]

# Geography Bundle (NEW 2025-12-24, Spatial Analysis with GF(3) Coloring)
# Key insight: Earth's surface is a 2-manifold; projections are functors
# Geohashes provide hierarchical spatial indexing with deterministic colors
# OSM topology validates network consistency
osm-topology (-1) ⊗ duckdb-spatial (0) ⊗ map-projection (+1) = 0 ✓  [Spatial SQL]
osm-topology (-1) ⊗ geodesic-manifold (0) ⊗ geohash-coloring (+1) = 0 ✓  [Spherical]
osm-topology (-1) ⊗ acsets (0) ⊗ gay-mcp (+1) = 0 ✓  [Graph Coloring]
three-match (-1) ⊗ duckdb-spatial (0) ⊗ geohash-coloring (+1) = 0 ✓  [H3 Indexing]
three-match (-1) ⊗ geodesic-manifold (0) ⊗ map-projection (+1) = 0 ✓  [Great Circles]
persistent-homology (-1) ⊗ duckdb-spatial (0) ⊗ geohash-coloring (+1) = 0 ✓  [Topological GIS]

# MDM Cobordism Bundle (NEW 2025-12-24, Auth Manifolds as State Transitions)
# Key insight: Auth is cobordism W: ∂₀ → ∂₁, not event sequence
# Enrollment chain: W₁(+1) → W₂(0) → W₃(-1) → W₄(+1) → W₅(-1) = 0
# Philosophy: No demos (credentials derive, not perform)
keychain-secure (-1) ⊗ mdm-cobordism (0) ⊗ gay-mcp (+1) = 0 ✓  [Credential Derivation]
temporal-coalgebra (-1) ⊗ mdm-cobordism (0) ⊗ oapply-colimit (+1) = 0 ✓  [State Observation]
sheaf-cohomology (-1) ⊗ mdm-cobordism (0) ⊗ koopman-generator (+1) = 0 ✓  [Pattern Learning]
three-match (-1) ⊗ mdm-cobordism (0) ⊗ gay-mcp (+1) = 0 ✓  [Enrollment Chain]
keychain-secure (-1) ⊗ unworld (0) ⊗ oapply-colimit (+1) = 0 ✓  [Keychain Derivation]

# Cat# Video Extraction Bundle (NEW 2025-12-24, from Spivak ACT 2023)
# Key insight: Cat# = Comod(P) where P = (Poly, y, ◁)
# Horizontal morphisms = bicomodules = pra-functors = data migrations
# Video: reference/videos/spivak_cat_sharp.mkv (16 slides, 31.7 min)
# Database: tensor_skill_paper.duckdb (v_catsharp_* views)
temporal-coalgebra (-1) ⊗ asi-polynomial-operads (0) ⊗ free-monad-gen (+1) = 0 ✓  [Poly Comonads]
yoneda-directed (-1) ⊗ kan-extensions (0) ⊗ oapply-colimit (+1) = 0 ✓  [Mac Lane Universal]
structured-decomp (-1) ⊗ acsets (0) ⊗ operad-compose (+1) = 0 ✓  [Cat# Bicomodules]
sheaf-cohomology (-1) ⊗ dialectica (0) ⊗ operad-compose (+1) = 0 ✓  [Three Homes]
persistent-homology (-1) ⊗ algebraic-dynamics (0) ⊗ operad-compose (+1) = 0 ✓  [Wiring Diagrams]
segal-types (-1) ⊗ acsets (0) ⊗ topos-generate (+1) = 0 ✓  [Nerves & Elements]
```

## Skill Loading Commands

```bash
# Show all triads with GF(3) conservation
just synergistic-triads

# Find triads containing a specific skill
just triads-for unworld
just triads-for acsets

# Get subagent assignment for a task domain
just subagent-for derivation
just subagent-for color
just subagent-for game
```

## Subagent Determination Logic

Given a task domain, the system:
1. Finds canonical triads that match the domain
2. Assigns skills to subagents based on trit polarity
3. Returns colored assignments with action verbs

Example for `:derivation` domain:
```ruby
{
  triad: ["three-match", "unworld", "gay-mcp"],
  subagents: [
    { skill: "gay-mcp", subagent: :generator, color: "#D82626" },
    { skill: "three-match", subagent: :validator, color: "#2626D8" },
    { skill: "unworld", subagent: :coordinator, color: "#26D826" }
  ],
  gf3_sum: 0
}
```

## Replacement Skills

Skills with the same trit can substitute for each other in triads:

- **MINUS (-1)**: three-match, slime-lisp, clj-kondo-3color, hatchery-papers, proofgeneral-narya, sheaf-cohomology, temporal-coalgebra, persistent-homology, cubes, cactus, gravity, cohomology-obstruction, spined-categories, bumpus-width, influence-propagation, polyglot-spi, dmd-spectral, interval-presheaf, schema-validation, ramanujan-expander, keychain-secure, **osm-topology**
- **ERGODIC (0)**: unworld, world-hopping, acsets, glass-bead-game, epistemic-arbitrage, kan-extensions, dialectica, open-games, discohy-streams, thread, lhott-cohesive-linear, asi-polynomial-operads, condensed-analytic-stacks, abductive-repl, entropy-sequencer, cognitive-surrogate, lispsyntax-acset, structured-decomp, algebraic-dynamics, deepwiki-mcp, ihara-zeta, compositional-acset-comparison, ies, mdm-cobordism, **duckdb-spatial**, **geodesic-manifold**
- **PLUS (+1)**: gay-mcp, cider-clojure, geiser-chicken, rubato-composer, free-monad-gen, operad-compose, topos-generate, little-disks, modular, swiss-cheese, libkind-directed, pattern-runs-on-matter, open-games-arena, free-monad-trees, agent-o-rama, pulse-mcp-stream, koopman-generator, oapply-colimit, colimit-reconstruct, moebius-inversion, **map-projection**, **geohash-coloring**

## Integration with Music Topos

The triadic structure mirrors the core patterns:
- **SplitMixTernary**: Tripartite streams (MINUS, ERGODIC, PLUS)
- **Unworld**: Derivation chains with GF(3) balanced
- **3-MATCH**: Colored subgraph isomorphism with GF(3) = 0
- **Glass Bead Game**: Badiou triangle with three polarities

## Available Skills (99+)

See `.agents/skills/` for symlinks to all skill definitions in `.ruler/skills/`.
