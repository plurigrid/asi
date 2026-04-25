---
name: alife-commons
description: "Artificial Life atlas covering open-ended evolution, chemical reaction networks, morphogenesis, self-replication, and programmable chemistry. Use when picking a simulation framework, wiring ALife models into the skill graph, or onboarding contributors to the ALife cluster."
trit: 0
---

# alife-commons

A single entry point that intermixes every ALife-primary skill in the repo.
Edges emitted below make each family member depth-1 from this hub.

Tree decomposition of the ALIFE 2025 theme graph yields **7 bags, tree-width 2**.
`evolution` is the universal adhesion vertex (appears in 6/7 bags).

## Families

### open-ended-evolution

`alife` · `alife2025` · `truealife` · `true-alife` · `jaxlife-open-ended` · `skill-evolution`

Comprehensive index: `alife` (256+ repos). Proceedings: `alife2025` (337 pages, 80+ papers).
JAX simulator: `jaxlife-open-ended`. Self-indexing automata: `true-alife`.
Skill-level evolution patterns: `skill-evolution`. Energy tracking: `truealife`.

### chemical-reaction-networks

`catalyst-chemical` · `chemical-abstract-machine` · `chemical-organization-theory` · `crn-topology` · `turing-chemputer`

Catalyst.jl ODE modeling: `catalyst-chemical`. Berry-Boudol CHAM: `chemical-abstract-machine`.
Org theory / closure: `chemical-organization-theory`. Reaction graph topology: `crn-topology`.
Programmable synthesis (XDL): `turing-chemputer`.

### morphogenesis-and-growth

`lindenmayer-systems` · `phyllotaxis`

L-systems for fractal/plant generation: `lindenmayer-systems`.
Golden-angle succulent growth as propagator network: `phyllotaxis`.

### self-organization

`autopoiesis` · `social-emergence-protocol`

Varela-inspired self-modifying agents: `autopoiesis`.
Stigmergic bootstrapping of complex social behaviors: `social-emergence-protocol`.

### complexity-measurement

`assembly-index`

Cronin's Assembly Theory for molecular complexity and life detection.

### protocol-evolution

`protocol-evolution-markets`

Prediction markets for protocol standard survival/fork/merge dynamics.

## Cross-family threading

- **CRN <-> Evolution:** `catalyst-chemical` models reaction dynamics that `alife2025` papers analyze for open-endedness (Bags 1,2 in tree decomposition).
- **Morphogenesis <-> Evolution:** `lindenmayer-systems` + `phyllotaxis` produce phenotypes that `jaxlife-open-ended` evaluates for fitness.
- **Self-org <-> CRN:** `autopoiesis` closure conditions map to `chemical-organization-theory` organizational closure.
- **Complexity <-> Evolution:** `assembly-index` provides the fitness landscape metric for `skill-evolution` and `protocol-evolution-markets`.
- **All <-> ALIFE 2025:** `alife2025` proceedings cover all families above; its 7-theme classification is the canonical reference.

## Cross-hub edges

- **para-mensch-commons:** `autopoiesis` bridges via cybernetic self-reference.
- **open-games:** `protocol-evolution-markets` uses open game semantics for market dynamics.
- **dynamic-sufficiency:** `chemical-organization-theory` closure maps to causal state gating.
- **acsets:** `crn-topology` and `catalyst-chemical` model reactions as attributed C-sets.
- **interaction-nets:** `chemical-abstract-machine` CHAM rules are interaction net reductions.
- **narya-proofs:** `assembly-index` complexity bounds admit formal verification.

## GF(3) theme balance

From the tree decomposition (7 bags, tree-width 2):

| Bag | Vertices | Trit sum | Status |
|-----|----------|----------|--------|
| 1 | evolution, emergence, CRN | +1+0-1 = 0 | balanced |
| 2 | evolution, CRN, morphogenesis | +1-1+0 = 0 | balanced |
| 3 | evolution, morphogenesis, self-replication | +1+0-1 = 0 | balanced |
| 4 | evolution, self-replication, complexity | +1-1+0 = 0 | balanced |
| 5 | evolution, complexity, cognition | +1+0-1 = 0 | balanced |
| 6 | evolution, cognition, emergence | +1-1+0 = 0 | balanced |
| 7 | emergence, CRN | +0-1 = -1 | rebalance via hub trit 0 |

Hub trit assignment: **0 (ERGODIC)** — coordinator role in the triadic system.

## Use when

- Picking a simulator or formalism for artificial life research
- Wiring a new ALife skill into the hub mesh
- Onboarding a contributor to the ALife cluster
- Cross-referencing ALIFE 2025 proceedings themes with existing skills
- Computing tree decompositions of theme graphs for GF(3) rebalancing
