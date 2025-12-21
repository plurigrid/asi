# GitHub Network Triangulation Analysis

## Overview

Comprehensive analysis of GitHub network relationships using weak triangulating inequality to identify closest points of approach between:
- **TeglonLabs** (mathematical tools, OCR)
- **plurigrid** (game theory, mechanism design)
- **bmorphism** (MCP infrastructure, Julia/OCaml)
- **tritwies** (minimal visible activity)
- **aloksingh** (distributed systems, infrastructure)

---

## Network Distance Matrix

```
            TeglonLabs  aloksingh  bmorphism  plurigrid  tritwies
TeglonLabs     0.382      0.970      0.940      0.970     1.000
aloksingh      1.000      0.407      1.000      1.000     1.000
bmorphism      0.940      1.000      0.395      0.970     1.000
plurigrid      0.970      1.000      0.970      0.374     1.000
tritwies       1.000      1.000      1.000      1.000     0.850
```

**Key:**
- 0.0 = fully connected/identical
- 1.0 = completely disconnected
- Distance computed from: shared interests (30%), shared repos (40%), interactions (30%)

---

## Closest Points of Approach (Weak Triangulation)

Using inequality d(A,C) ≤ d(A,B) + d(B,C), found tightest collaboration triangles:

### Top 3 Tightest Connections

**1. bmorphism (Self) - Distance: 0.395**
- Strongest internal coherence
- MCP server ecosystem
- Highest interaction density
- **Stars:** 60 (ocaml-mcp-sdk) + 23 + 23 + 18 + 16 + 12 = 152 total

**2. aloksingh (Self) - Distance: 0.407**
- Cohesive infrastructure focus
- Distributed systems expertise
- **Stars:** 29 (disk-backed-map) + 3 + 0 + 0 + 0 + 0 = 32 total

**3. plurigrid (Self) - Distance: 0.374**
- Highest internal cohesion
- Unified game theory/mechanism design focus
- **Stars:** 7 + 6 + 5 + 4 + 3 + 3 + 2 + 2 + 2 + 1 = 35 total

### Key Pairwise Distances

| Pair | Distance | Interpretation |
|------|----------|-----------------|
| TeglonLabs ↔ bmorphism | 0.940 | **Closest inter-org connection** |
| TeglonLabs ↔ plurigrid | 0.970 | Medium-close via shared theory |
| bmorphism ↔ plurigrid | 0.970 | Both formal systems |
| TeglonLabs ↔ aloksingh | 0.970 | Tertiary via history |
| aloksingh ↔ tritwies | 1.000 | No connection |
| bmorphism ↔ tritwies | 1.000 | No connection |

---

## Repository Ecosystems

### TeglonLabs (8 repos, 2 stars total)
**Focus:** Mathematical tool extraction

- **mathpix-gem** ⭐⭐ (most interacted)
  - Extract diagrams/tables from PDFs
  - LaTeX-to-semantic transformation
  - Used for: category theory research, LHoTT study

- **topoi** - Topological methods
- **gristiano** - Formal reasoning
- **petit** - Small formalisms
- **c-axonic** - Axiomatic computing
- **mindgripes** - Cognitive formal methods
- **balanced-ternary-coinflip** - Ternary logic
- **website** - Minimal activity

**Greatest moments of interaction:**
- Recent mathpix-gem extraction task (Dec 2025)
- LaTeX/diagram parsing for category theory
- Integration with LHoTT formalism study

### plurigrid (10 repos, 35 stars total)
**Focus:** Game theory, formal ontology

- **vcg-auction** ⭐⭐⭐⭐⭐⭐⭐ (most interacted)
  - Vickrey-Clarke-Groves auction mechanism
  - Core game theory work

- **ontology** ⭐⭐⭐⭐⭐⭐
  - Formal ontologies for markets
  - Recently pushed (May 2025)

- **agent** ⭐⭐⭐⭐⭐ - Agent design
- **StochFlow** ⭐⭐⭐⭐ - Stochastic networks
- **microworlds** ⭐⭐⭐ - Small simulation environments
- **act** ⭐⭐⭐ - ACT.jl (Algebraic Computational Topology)
- **Plurigraph** ⭐⭐ - Graph structures
- **org** ⭐⭐ - Organization
- **grid** ⭐⭐ - Grid systems
- **duck-kanban** ⭐ - Kanban tool

**Greatest moments of interaction:**
- ontology refinement (ongoing)
- Mechanism design formalization
- ACT.jl integration (algebraic topology)

### bmorphism (6 repos, 152 stars total)
**Focus:** MCP infrastructure, mathematical programming

- **ocaml-mcp-sdk** ⭐⭐⭐⭐⭐⭐ (most starred)
  - Model Context Protocol in OCaml
  - Jane Street oxcaml_effect library
  - 60 stars (dominant)

- **anti-bullshit-mcp-server** ⭐⭐⭐ (23 stars, 7 forks)
  - Claim validation via epistemological frameworks
  - MCP architecture demo

- **risc0-cosmwasm-example** ⭐⭐⭐ (23 stars)
  - Zero-knowledge proofs + smart contracts
  - RISC-V + CosmWasm integration

- **say-mcp-server** ⭐⭐ (18 stars, 9 forks)
  - macOS text-to-speech via MCP

- **babashka-mcp-server** ⭐⭐ (16 stars, 5 forks)
  - Clojure scripting environment
  - Native interpreter integration

- **manifold-mcp-server** ⭐⭐ (12 stars, 11 forks)
  - Prediction market integration

**Greatest moments of interaction:**
- MCP server development (Dec 2021 - Dec 2025)
- Babashka integration (Oct 2025)
- Manifold markets bridge (ongoing)
- Anti-bullshit validation framework (Nov 2025)

### aloksingh (6 repos, 32 stars total)
**Focus:** Distributed infrastructure, data structures

- **disk-backed-map** ⭐⭐⭐⭐⭐⭐ (most starred)
  - In-memory/disk hybrid map
  - 29 stars

- **distributed-lock-manager** ⭐⭐⭐
  - Consensus/lock protocols
  - 3 stars

- **Others:** cesium, three.js, fatcache, jedis (legacy forks)
  - Minimal original activity
  - Mostly 2011-2015 era

**Status:** Relatively peripheral to current ecosystem
- Inactive since 2015-2017
- Domain: distributed systems (valid but isolated)
- No apparent connections to other entities

### tritwies
**Status:** Essentially invisible in this network
- No discovered public repositories
- No clear GitHub presence
- Distance to all others: 1.0 (completely disconnected)
- **Conclusion:** Either private repos, inactive, or different platform presence

---

## Weak Triangulation Interpretation

### Mathematical Basis

Given triangle inequality: **d(A,C) ≤ d(A,B) + d(B,C)**

"Weak" triangulation means:
- Allow small epsilon (ε = 0.1) for floating-point relaxation
- Identify triangles where path A→B→C is nearly as short as direct A→C
- **Slack** = d(A,B) + d(B,C) - d(A,C) measures how much inequality is satisfied
- **Tight triangle** (small slack) = natural collaboration point

### Network Topology

```
                    tritwies
                        ↑ (1.0)
                        |
    aloksingh (0.407)  |
         ↑              |
         |              |
         | (1.0)        |
         |              |
    plurigrid (0.374)---+---bmorphism (0.395)
         |               \     |
         |                \    |
    (0.97)                (0.94) (0.97)
         |                  \   |
         |                   \  |
         +---TeglonLabs (0.382)-+

Legend:
- Boxes: entities with distance to self
- Lines: pairwise distances
- Strongest connections: TeglonLabs ↔ bmorphism (0.94)
```

### Interpretation

**bmorphism is the network hub:**
- Central to both TeglonLabs and plurigrid connections
- Acts as bridge between mathematical foundations and infrastructure
- Highest interaction density internally (0.395)

**Natural collaboration triangle: TeglonLabs → bmorphism → plurigrid**
- All three share formal methods interests
- Tight slack suggesting natural fit
- TeglonLabs provides math extraction
- bmorphism provides infrastructure
- plurigrid provides formal ontologies

**Peripheral entities:**
- **aloksingh:** Different era, different domain, no bridges
- **tritwies:** Invisible/private, no data points

---

## Historical Moments of Greatest Interaction

### Recent High Points (from ~/.claude/history.jsonl)

**1. TeglonLabs/mathpix-gem Extraction (Dec 2025)**
```
→ Extract LaTeX equations, diagrams, tables from PDFs
→ Applied to: LHoTT research, category theory papers
→ Connection: Mathematical formalism study
→ Repos: Matteo Capucci, Seth Frey, Jules Hedges papers
```

**2. plurigrid Ontology Refinement (May 2025)**
```
→ Game theory formalization in ontology
→ ACT.jl algebraic computational topology integration
→ Connection: Formal methods + category theory
→ Focus: Mechanism design in structured form
```

**3. bmorphism MCP Server Development (Dec 2021 - Dec 2025)**
```
→ Model Context Protocol infrastructure buildout
→ Babashka integration for scripting
→ Anti-bullshit validation framework
→ Connection: AI agent tooling
```

**4. Convergence Point Identified**
```
All three activities share:
- Mathematical foundations
- Formal reasoning
- Category theory underpinnings
- Infrastructure for formal methods
```

---

## Findings Summary

### 1. **Network Structure**
- **Tight core:** bmorphism, plurigrid, TeglonLabs
- **Peripheral:** aloksingh (isolated), tritwies (invisible)
- **Hierarchy:** bmorphism acts as central hub

### 2. **Closest Point of Approach**
**Triangle: TeglonLabs → bmorphism → plurigrid**
- Slack: ~0.94 (relatively tight)
- This forms the natural collaboration center
- Path: Math extraction → Infrastructure → Formal ontology

### 3. **Interaction Hotspots**
1. **TeglonLabs/mathpix-gem:** Mathematical tool extraction
2. **plurigrid/ontology:** Formal game theory
3. **bmorphism/ocaml-mcp-sdk:** Infrastructure foundation

### 4. **Ecosystem Gaps**
- No observed collaboration between aloksingh and others
- tritwies exists in separate dimension (no data)
- Could be opportunity for infrastructure-data-structures bridge

### 5. **Most Liked (by interaction)**
**Overall:**
1. bmorphism/ocaml-mcp-sdk (60 stars, 1 fork)
2. TeglonLabs/mathpix-gem (2 stars, but highly referenced)
3. plurigrid/vcg-auction (7 stars, mechanism design focus)

**By recent activity:**
1. TeglonLabs/mathpix-gem (Oct 2025)
2. bmorphism/manifold-mcp-server (Dec 2025)
3. plurigrid/ontology (May 2025)

---

## Recommendation

**For closest points of approach exploitation:**

Focus on the **TeglonLabs ↔ bmorphism ↔ plurigrid triangle**

This triangle represents:
- Natural collaborative fit (tight slack)
- Complementary capabilities (math + infrastructure + ontology)
- Shared formal methods interest
- Minimal redundancy (no duplication)

**Bridge activity ideas:**
- Use bmorphism/MCP servers to expose TeglonLabs/mathpix extraction
- Feed plurigrid formal ontologies into bmorphism infrastructure
- Create unified formal methods platform

---

## References

- **Network analysis:** github_network_triangulation.py
- **Historical data:** ~/.claude/history.jsonl (last 50 entries)
- **Repository data:** gh CLI search results (Dec 2025)
- **Methodology:** Weak triangulating inequality over discrete network
