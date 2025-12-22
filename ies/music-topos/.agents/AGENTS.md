# Synergistic 3-Tuples: Skill Loading with GF(3) Conservation

## Overview

Skills are loaded via symlinks from `.ruler/skills/` to `.agents/skills/`. Each skill has a **trit assignment** (-1, 0, +1) that enables **GF(3) conservation** when skills are combined in triads.

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

- **MINUS (-1)**: three-match, slime-lisp, clj-kondo-3color, hatchery-papers, proofgeneral-narya, sheaf-cohomology, temporal-coalgebra, persistent-homology, cubes, cactus, gravity, cohomology-obstruction, spined-categories, bumpus-width, influence-propagation, polyglot-spi, dmd-spectral, interval-presheaf, schema-validation
- **ERGODIC (0)**: unworld, world-hopping, acsets, glass-bead-game, epistemic-arbitrage, kan-extensions, dialectica, open-games, discohy-streams, thread, lhott-cohesive-linear, asi-polynomial-operads, condensed-analytic-stacks, abductive-repl, entropy-sequencer, cognitive-surrogate, lispsyntax-acset, structured-decomp, algebraic-dynamics
- **PLUS (+1)**: gay-mcp, cider-clojure, geiser-chicken, rubato-composer, free-monad-gen, operad-compose, topos-generate, little-disks, modular, swiss-cheese, libkind-directed, pattern-runs-on-matter, open-games-arena, free-monad-trees, agent-o-rama, pulse-mcp-stream, koopman-generator, oapply-colimit, colimit-reconstruct

## Integration with Music Topos

The triadic structure mirrors the core patterns:
- **SplitMixTernary**: Tripartite streams (MINUS, ERGODIC, PLUS)
- **Unworld**: Derivation chains with GF(3) balanced
- **3-MATCH**: Colored subgraph isomorphism with GF(3) = 0
- **Glass Bead Game**: Badiou triangle with three polarities

## Available Skills (29)

See `.agents/skills/` for symlinks to all skill definitions in `.ruler/skills/`.
