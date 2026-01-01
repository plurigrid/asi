# CatColab Integration Guide

## Overview

CatColab is the Topos Institute's platform for **collaborative category theory**. It integrates with the ACSet skill ecosystem as the primary schema authoring environment.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                      CatColab Platform                       │
│  ├── Double Theories (DOTS)                                  │
│  ├── Automerge CRDT (real-time collaboration)               │
│  └── catlog Rust Engine (WASM)                              │
├─────────────────────────────────────────────────────────────┤
│                     ACSet Skills Layer                       │
│  ├── acsets (core schema)                                   │
│  ├── compositional-acset-comparison (DB interop)            │
│  └── lispsyntax-acset (S-expr bridge)                       │
├─────────────────────────────────────────────────────────────┤
│                   Categorical Partners                       │
│  ├── structured-decomp (sheaves on decompositions)          │
│  ├── sheaf-cohomology (Čech verification)                   │
│  └── kan-extensions (universal constructions)               │
└─────────────────────────────────────────────────────────────┘
```

## GF(3) Triad Pattern

CatColab acts as coordinator (trit=0) between validation and generation:

```
sheaf-cohomology (-1) ⊗ topos-catcolab (0) ⊗ datalog-fixpoint (+1) = 0 ✓
```

| Role | Trit | Skills |
|------|------|--------|
| **Validation** | -1 | sheaf-cohomology, kan-extensions, persistent-homology |
| **Coordination** | 0 | topos-catcolab, acsets, structured-decomp |
| **Generation** | +1 | datalog-fixpoint, free-monad-gen |

## Usage Patterns

### 1. Schema Design in CatColab → ACSet Export

```julia
using Catlab, ACSets

# Design in CatColab's visual editor, then export:
@present ThStockFlow(FreeSchema) begin
  Stock::Ob
  Flow::Ob
  Link::Ob
  src::Hom(Flow, Stock)
  tgt::Hom(Flow, Stock)
  lsrc::Hom(Link, Stock)
  ltgt::Hom(Link, Stock)
end

# Instantiate as ACSet
const StockFlow = ACSetType(ThStockFlow)
sir = @acset StockFlow begin
  Stock = 3  # S, I, R
  Flow = 2   # infection, recovery
end
```

### 2. Collaborative Modeling Session

```typescript
// CatColab real-time session
interface ModelSession {
  theory: 'StockFlow' | 'Petri' | 'RegNet';
  participants: User[];
  document: AutomergeDoc<ModelNotebook>;
  
  // Sync changes across all editors
  onEdit(cell: CellEdit): void {
    this.document.change(doc => {
      applyEdit(doc.cells, cell);
    });
  }
}
```

### 3. P-adic Embedding for Skill Discovery

```python
from padic_ultrametric import PAdicSkillIndex

# Index skills with ultrametric distance
index = PAdicSkillIndex('~/.claude/skills', seed=1069, prime=2)
index.index_skills_with_ids()

# Find categorical neighbors of catcolab
neighbors = index.padic_nearest('topos-catcolab', k=5)
# → [('structured-decomp', 0.12, 0.0625),
#    ('acsets', 0.18, 0.125),
#    ('sheaf-cohomology', 0.21, 0.25)]
```

## The 15 ACSet Skills

| Skill | Domain | Integration |
|-------|--------|-------------|
| `acsets` | Core | Schema foundation |
| `acsets-relational-thinking` | Theory | Categorical DBs |
| `browser-history-acset` | Browser | Web navigation |
| `calendar-acset` | Google Calendar | Time management |
| `chatgpt-export-acset` | OpenAI | Conversation export |
| `compositional-acset-comparison` | DuckDB/Lance | DB comparison |
| `docs-acset` | Google Docs | Document tracking |
| `drive-acset` | Google Drive | File management |
| `lispsyntax-acset` | S-expressions | Code structure |
| `nix-acset-worlding` | Nix store | Package deps |
| `openai-acset` | OpenAI schema | API modeling |
| `protocol-acset` | P2P protocols | Network topology |
| `rg-flow-acset` | Ripgrep | Search flows |
| `specter-acset` | Navigation | Path lenses |
| `tasks-acset` | Google Tasks | Todo tracking |

## Color Assignments (seed=1069)

```
topos-catcolab:     #4A90D9 (blue, coordinator)
acsets:             #E67F86 (warm pink)
structured-decomp:  #D06546 (burnt sienna)
sheaf-cohomology:   #1316BB (deep blue)
datalog-fixpoint:   #8DDC7B (mint green)
```

## References

- [CatColab Platform](https://catcolab.topos.institute)
- [Catlab.jl Documentation](https://algebraicjulia.github.io/Catlab.jl)
- [ACSets.jl](https://github.com/AlgebraicJulia/ACSets.jl)
- [StructuredDecompositions.jl](https://github.com/AlgebraicJulia/StructuredDecompositions.jl)
