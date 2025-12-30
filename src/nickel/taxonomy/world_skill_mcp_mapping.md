# World ↔ Skill ↔ MCP Mapping

> GF(3)-conserving triadic assignment of worlds to skills and MCPs

## Seed: 137508 (Golden Angle)

## GF(3) Role Distribution

| Trit | Role | Symbol | Worlds |
|------|------|--------|--------|
| +1 | GENERATOR | ⊕ | B, K, T, e, m, q |
| 0 | COORDINATOR | ○ | A, G, S, d, l, o, v |
| -1 | VALIDATOR | ⊖ | F, P, c, h, n, r |

## World Repository Counts

```
World d: 108 repos  █████████████████████
World v:  76 repos  ███████████████
World c:  59 repos  ███████████
World m:  57 repos  ███████████
World F:  44 repos  ████████
World B:  23 repos  ████
World A:  17 repos  ███
World G:  11 repos  ██
World o:  11 repos  ██
World T:   9 repos  █
World r:   9 repos  █
World l:   8 repos  █
World h:   6 repos  █
World P:   4 repos
World e:   4 repos
World S:   3 repos
World n:   3 repos
World K:   2 repos
World q:   1 repos
```

## GF(3) Conservation Triads

### Triad 1: Move/Blockchain Society
```
m(+1) ⊗ d(0) ⊗ n(-1) = 0 ✓

GENERATOR:   World m — move, aptos-core, sui, movemate
COORDINATOR: World d — babashka, duckdb, clay
VALIDATOR:   World n — narya, nlab-content, topos_papers
```

### Triad 2: Category Theory Society
```
B(+1) ⊗ A(0) ⊗ P(-1) = 0 ✓

GENERATOR:   World B — bmorphism, AlgebraicPetri.jl, WiringDiagrams.jl
COORDINATOR: World A — ACSets.jl, Catlab.jl, Decapodes.jl
VALIDATOR:   World P — asi, plurigrid
```

### Triad 3: Topos Institute Society
```
T(+1) ⊗ v(0) ⊗ r(-1) = 0 ✓

GENERATOR:   World T — CatColab, poly, Tritwies
COORDINATOR: World v — 1lab, Dialectica, HoTT
VALIDATOR:   World r — rzk, sHoTT, complexity-scaling
```

### Triad 4: Clojure/Lisp Society
```
e(+1) ⊗ S(0) ⊗ c(-1) = 0 ✓

GENERATOR:   World e — emacs, elisp
COORDINATOR: World S — Spritely, Scheme, Goblins
VALIDATOR:   World c — clojure, clj-kondo
```

## Complete Mapping Table

| World | Role | Color | MCP | Primary Skill |
|-------|------|-------|-----|---------------|
| m (+1) | GENERATOR | #D7D085 | gay, babashka | aptos-gf3-society |
| d (0) | COORDINATOR | #C30F2D | firecrawl, exa | datalog-fixpoint |
| n (-1) | VALIDATOR | #E146A8 | deepwiki | narya-proofs |
| B (+1) | GENERATOR | #77DEB1 | gay, tree-sitter | bmorphism-interactome |
| A (0) | COORDINATOR | #B0285F | babashka | acset-taxonomy |
| P (-1) | VALIDATOR | #D6DB4C | firecrawl | cognitive-superposition |
| T (+1) | GENERATOR | #AF100A | deepwiki | topos-catcolab |
| v (0) | COORDINATOR | #65DBDE | exa | lhott-cohesive-linear |
| r (-1) | VALIDATOR | #8E7526 | gay | cargo-rust |

## Move Triad MC Sweep Colors

From `mc_sweep(n_sweeps=4, n_workers=3, seed=137508)`:

### Worker 1: aptos-gf3-society (+1 GENERATOR)
- Seed: `11400714819323061553`
- Sweep 1: `#8A60CB` — propose()
- Sweep 2: `#64E87E` — create()
- Sweep 3: `#68EFD4` — stake()
- Sweep 4: `#2339B9` — execute()

### Worker 2: move-narya-bridge (0 COORDINATOR)
- Seed: `4354685564936970510`
- Sweep 1: `#3A86AF` — mediate()
- Sweep 2: `#15C2BA` — vote()
- Sweep 3: `#8664DE` — coordinate()
- Sweep 4: `#2C319E` — bridge()

### Worker 3: move-smith-fuzzer (-1 VALIDATOR)
- Seed: `15755400384259910939`
- Sweep 1: `#BDCA5B` — verify()
- Sweep 2: `#B3DE2A` — challenge()
- Sweep 3: `#85259D` — audit()
- Sweep 4: `#11B597` — fuzz()

## Aptos Society Module Integration

```
gf3.move         — Trit primitives from world index
society.move     — World directories as member addresses
governance.move  — Cross-world proposals
staking.move     — Repo count as stake weight
```

## Skill Orchestration Pipeline

```
┌────────────┐     ┌────────────┐     ┌────────────┐     ┌────────────┐
│   SKILL    │────▶│    MCP     │────▶│   WORLD    │────▶│   APTOS    │
│            │     │            │     │            │     │  SOCIETY   │
└────────────┘     └────────────┘     └────────────┘     └────────────┘
      │                 │                  │                   │
      ▼                 ▼                  ▼                   ▼
aptos-gf3-      gay-mcp (color)    World m (move)     governance.move
society         babashka (exec)    World n (verify)   society.move
(+1 GEN)        firecrawl (web)    World d (query)    staking.move
                exa (search)       World A (acsets)   gf3.move
                deepwiki (docs)
```

## MCP Inventory

| MCP | Function | Trit Assignment |
|-----|----------|-----------------|
| gay | Deterministic colors | +1 (generates colors) |
| babashka | Clojure execution | 0 (coordinates scripts) |
| firecrawl | Web scraping | -1 (validates content) |
| exa | Web search | 0 (coordinates queries) |
| deepwiki | GitHub docs | -1 (validates repos) |
| tree-sitter | AST parsing | +1 (generates structure) |

## References

- [SplitMix64 Implementation](./splitmix64_implementation.md)
- [MINUS Skill Lattice](./minus_skill_lattice.md)
- [Aptos GF(3) Society Skill](/Users/bob/.claude/skills/aptos-gf3-society/SKILL.md)
- [Gay.jl Source](https://github.com/bmorphism/Gay.jl)

---

**Generated**: 2025-12-30
**Seed**: 137508 (Golden Angle: 137.508°)
**GF(3) Sum**: 0 ✓
