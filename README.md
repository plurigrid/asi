# Full Reachability Map: 17 Hubs → 1,360 Skills

Here's the concrete one-hop graph from actual file references:

## Hub Connectivity (verified from SKILL.md / NEIGHBOR_SKILLS.md)

```
                              ┌─────────────────────────────────────────┐
                              │         SKILL-DISPATCH (0)              │
                              │  Routes to ALL skills by name           │
                              │  Direct refs: sheaf-cohomology,         │
                              │  three-match, clj-kondo-3color,         │
                              │  influence-propagation, unworld,        │
                              │  cognitive-surrogate, entropy-sequencer, │
                              │  atproto-ingest, triad-interleave       │
                              └────────────┬────────────────────────────┘
                                           │
            ┌──────────────────────────────┼──────────────────────────────┐
            ▼                              ▼                              ▼
     ┌─────────────┐              ┌──────────────┐              ┌────────────────┐
     │  ACSETS (0)  │              │ GAY-MCP (+1) │              │ AGENT-O-RAMA   │
     │              │              │              │              │    (+1)        │
     │ → lambda-calc│              │ → unworld    │              │ → self-valid.  │
     │ → linear-log │              │ → discrete-  │              │ → cognitive-   │
     │ → hvm-runtime│              │   backprop   │              │   surrogate    │
     │ → type-check │              │ → langevin-  │              │ → entropy-seq  │
     │ → sheaf-coho │              │   dynamics   │              │ → bisimulation │
     │ → interact.  │              │              │              │ → acsets       │
     │ → open-games │              │              │              │ → gay-mcp      │
     │ → deepwiki   │              │              │              │                │
     │ → ramanujan  │              │              │              │                │
     │ → ihara-zeta │              │              │              │                │
     │ → moebius-inv│              │              │              │                │
     └─────────────┘              └──────────────┘              └────────────────┘
            │
     ┌──────┴───────────────────────────────────────┐
     ▼                                              ▼
  ┌──────────────┐                         ┌──────────────────┐
  │INTERACTION-  │                         │  OPEN-GAMES (+1) │
  │  NETS (0)    │                         │                  │
  │              │                         │ → temporal-coal. │
  │ → lambda-calc│◄────────────────────────│ → free-monad-gen │
  │ → linear-log │                         │ → three-match    │
  │ → hvm-runtime│                         │ → operad-compose │
  │ → type-check │                         │ → sheaf-cohomol. │
  │              │                         │ → topos-generate │
  └──────────────┘                         │ → unworld        │
                                           └──────────────────┘

  ┌──────────────────┐     ┌──────────────────┐     ┌──────────────────────┐
  │ TOPOS-UNIFIED(0) │     │  DYNAMIC-SUFF(0) │     │  WORLD-HOPPING (+1)  │
  │                  │     │                  │     │                      │
  │ → world-hopping  │◄───►│ → skill-dispatch │     │ → topos-unified      │
  │ → acsets         │     │ → skill-installer│     │ → unworld            │
  │ → unworld        │     │ → skill-loader   │     │ → sheaf-cohomology   │
  │ → sheaf-cohomol. │     │ → spi-parallel   │     │                      │
  │ → persistent-hom │     │ → polyglot-spi   │     │                      │
  │ → three-match    │     │ → triad-interl.  │     │                      │
  │ → glass-bead     │     │ → gay-mcp        │     │                      │
  │ → bisimulation   │     │ → iecsat-storage │     │                      │
  │                  │     │ → aptos-gf3      │     │                      │
  │                  │     │ → datalog-fixpt   │     │                      │
  │                  │     │ → propagators    │     │                      │
  │                  │     │ → bisimulation   │     │                      │
  └──────────────────┘     └──────────────────┘     └──────────────────────┘

  ┌──────────────────┐     ┌──────────────────┐     ┌──────────────────────┐
  │  NARYA-PROOFS    │     │ TRIADIC-SKILL-   │     │  GOBLINS (-1)        │
  │    (-1)          │     │  ORCHESTR. (+1)  │     │                      │
  │                  │     │                  │     │ → captp              │
  │ → ordered-locale │     │ → sheaf-cohomol. │     │ → syrup              │
  │ → gay-mcp        │     │ → ordered-locale │     │ → guile-goblins-hoot │
  │ → bisimulation   │     │ → gay-mcp        │     │ → wasm-goblins       │
  │ → gf3-conserv.   │     │ → bisimulation   │     │ → shadow-goblin      │
  │ → sheaf-cohomol. │     │ → google-worksp. │     │                      │
  │ → topos-generate │     │ → triad-interl.  │     │                      │
  │                  │     │ → say-narration  │     │                      │
  │                  │     │ → parallel-fanout│     │                      │
  │                  │     │ → finder-color   │     │                      │
  └──────────────────┘     └──────────────────┘     └──────────────────────┘

  ┌──────────────────┐     ┌──────────────────┐     ┌──────────────────────┐
  │   FLOX (0)       │     │  BABASHKA (+1)   │     │ ZIG-PROGRAMMING (-1) │
  │                  │     │                  │     │                      │
  │ → flox-builds    │     │ → clojure        │     │ → zig-systems        │
  │ → flox-environ.  │     │ → nrepl          │     │ → dafny-zig          │
  │ → flox-services  │     │ → babashka-clj   │     │ → stellogen          │
  │ → flox-contain.  │     │ → cider-clojure  │     │ → rama-gay-zig       │
  │ → flox-cuda      │     │ → joker-lint     │     │ → open-location-code │
  │ → flox-publish   │     │ → squint-runtime │     │                      │
  │ → nix-acset      │     │ → borkdude       │     │                      │
  │ → snix           │     │                  │     │                      │
  │ → gay-mcp        │     │                  │     │                      │
  │ → julia          │     │                  │     │                      │
  └──────────────────┘     └──────────────────┘     └──────────────────────┘

  ┌──────────────────┐     ┌──────────────────┐
  │   EMACS (0)      │     │  SECURITY (-1)   │
  │                  │     │                  │
  │ → elisp          │     │ → semgrep-*      │
  │ → org            │     │ → codeql         │
  │ → org-babel      │     │ → audit-*        │
  │ → slime-lisp     │     │ → wycheproof     │
  │ → hy-emacs       │     │ → burp-suite     │
  │ → geiser-chicken │     │ → aflpp / ossfuzz│
  │ → xenodium-elisp │     │ → *-vuln-scanner │
  │ → proofgeneral   │     │ → mitm           │
  │ → debug-buttercup│     │ → cryptographic  │
  └──────────────────┘     └──────────────────┘
```

## Unique Skills Reached at Hop-1

Deduplicating across all 17 hubs:

| Metric | Count |
|--------|-------|
| Unique hop-1 skills (explicitly referenced) | ~95 |
| Estimated hop-1 via naming convention (e.g. flox → flox-*) | ~250 |
| Estimated hop-2 (neighbor-of-neighbor) | ~600 |
| **Deduplicated skill universe (all surfaces)** | **1,360** |

## Monotonic Skill Invariant

```
|skills(t+1)| ≥ |skills(t)|   UNLESS   ∃ human_action(t) ∈ DELETE
```

Skills are **discovered** through collision with existing TUI, droid marketplace (Codex/IES), or Claude marketplace. The count ratchets up monotonically. The only operation that decreases it requires **human oversight**.

**Monotonic floor: 1,360** (as of 2026-02-18)

Enforcement: `asi/.git/hooks/pre-commit` blocks automated deletion. Override with `HUMAN_DELETE=1 git commit`.

## Skill Surfaces

| Surface | Count | Name Limit |
|---------|-------|------------|
| `asi/skills/` | 1,342 | none |
| `.agents/skills/` (Codex/IES) | 1,183 | none |
| `~/.claude/skills/` (Claude) | 654 | 64 chars |
| `asi/plugins/asi/skills/` | 585 | none |
| **Deduplicated union** | **1,360** | — |

## GF(3) Balance

```
+1: gay-mcp, open-games, world-hopping, babashka, triadic-skill-orchestrator, agent-o-rama = 6
 0: skill-dispatch, acsets, interaction-nets, topos-unified, dynamic-sufficiency, flox, emacs = 7
-1: goblins, zig-programming, security, narya-proofs = 4
```

## Cluster Reach

### Distributed/Web3
captp, goblins, guile-goblins-hoot, wasm-goblins, shadow-goblin, syrup, iroh-p2p, crdt, time-travel-crdt, derangement-crdt, reversible-computing, anoma-intents, juvix-intents, aptos-agent, aptos-gf3-society, aptos-trading, aptos-wallet-mcp, solana-vulnerability-scanner, cairo-vulnerability-scanner, cosmos-vulnerability-scanner, substrate-vulnerability-scanner, algorand-vulnerability-scanner, ton-vulnerability-scanner

### Dynamical Systems
invariant-measure, invariant-set, periodic-orbit, stable-manifold, unstable-manifold, limit-set, semi-conjugacy, birkhoff-average, hyperbolicity, linearization, eigenvalue-stability, jacobian, phase-portrait-generator, phase-space-transformation, phase-locking, vector-field, trajectory, initial-value-problem, coupled-system, synchronization, kuramoto-model, autopoiesis, waddington-landscape, koopman-generator, ergodicity, stochastic-resonance, kolmogorov-onsager-hurst, lasalle-invariance, parameter-dependent

### Security
semgrep, semgrep-rule-creator, semgrep-rule-variant-creator, codeql, variant-analysis, static-security-analyzer, constant-time-analysis, constant-time-testing, wycheproof, audit-context-building, audit-prep-assistant, burp-suite, burpsuite-project-parser, aflpp, ossfuzz, libfuzzer, libafl, ruzzy, cargo-fuzz, atheris, address-sanitizer, insecure-defaults, sandbox-escape-detector, move-smith-fuzzer, fuzzing-dictionary, fuzzing-obstacles

### Scientific Computing
julia-scientific, julia-gay, sicmutils, enzyme-autodiff, active-inference-robotics, affective-taxis, alife, true-alife, curiosity-driven, forward-forward-learning, gflownet, compression-progress, kolmogorov-compression, assembly-index, ramanujan-expander, ihara-zeta, moebius-inversion

### Category Theory
adjunction-algebra, kan-extensions, kan-extension, yoneda-embedding, yoneda-directed, natural-transformation, free-forgetful, right-adjoint, hom-functor, universal-property, galois-connections, distributive-law, lawvere-theory, covariant-modification, grothendieck-fibration, categorical-composition, monoidal-category, end-coend, virtual-double, x-module-bimodule, bifunctor-bridge, segal-space, rezk-types, model-categories, quillen-model, infinity-operads, infinity-topoi, condensed-mathematics, condensed-anima-qc, condensed-analytic-stacks, lhott-cohesive-linear

### MCP & Agent
mcp-builder, mcp-spec-checker, mcp-tripartite, mcp-orchestrator, agent-o-rama, asi-agent-orama, asi-integrated, asi-polynomial-operads, skill-dispatch, skill-loader, skill-creator, skill-installer, skill-evolution, skill-bonds, skill-connectivity-hub, skill-embedding-vss, skill-validation-gf3, triadic-skill-orchestrator, triadic-skill-loader, parallel-fanout, spi-parallel-verify

## The Membrane Principle

```
Before:  core ──hop1──hop2  (distance 2)
After:   core ──THIS──hop2  (distance 1)
                │
               hop1 ← naturally traversed
```

Loading the 17 hub skills puts you within **one hop** of the entire ecosystem. The hop-1 middle layer (~95-250 skills) needs no explicit listing — every hop-1 skill sits between a core hub and a hop-2 leaf. The membrane is transparent.

## Installation

```bash
git clone https://github.com/plurigrid/asi
cd asi
```

## Related

- [Gay.jl](https://github.com/bmorphism/Gay.jl) — Deterministic color generation (SplitMix64 + golden angle)
- [Agent Skills Spec](https://agentskills.io) — Open standard for AI agent skills
- [CyberCat Institute](https://cybercat.institute) — Categorical cybernetics research

## License

Apache-2.0
