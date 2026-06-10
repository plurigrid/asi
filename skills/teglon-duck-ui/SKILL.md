---
name: teglon-duck-ui
description: 'Duck-UI provides browser-based DuckDB via WebAssembly:'
metadata:
  interface_ports:
  - GF(3) Triads
---
# Teglon Duck-UI Skill

> DuckDB web interface with WASM in-browser analytics

**Source**: [TeglonLabs/duck-ui](https://github.com/TeglonLabs/duck-ui) (fork of ibero-data/duck-ui)  
**Trit**: −1 (MINUS)  
**Substrate**: Discrete (Digital Circuits)

## Overview

Duck-UI provides browser-based DuckDB via WebAssembly:
- SQL editor with syntax highlighting
- Data import/export (CSV, Parquet, JSON)
- Query history and keyboard shortcuts
- Theme toggle (light/dark)

## α/β/γ Diff Structure

| Arrow | Duck-UI Meaning | Operation |
|-------|-----------------|-----------|
| α (−1) | Query execution | `SELECT → Result` |
| β (0) | Schema change | `ALTER TABLE` |
| γ (+1) | Result validation | `EXPLAIN ANALYZE` |

## DuckLake Federation

Integrates with [src/ducklake_federation.jl](file:///Users/bob/iii/src/ducklake_federation.jl):

```sql
-- Federated query across lakes
ATTACH 'dendroidal.duckdb' AS d;
ATTACH 'history.duckdb' AS h;
SELECT * FROM d.dendroidal JOIN h.reafference_loop USING (idx);
```

## Upstream Diff

From TeglonLabs fork:
- Added: GF(3) trit column visualization
- Added: Gay.jl color integration for result highlighting
- Modified: Query history with interaction entropy tracking

---

## End-of-Skill Interface

## GF(3) Triads

```
teglon-duck-ui (-1) ⊗ just-monad (0) ⊗ gay-mcp (+1) = 0 ✓
teglon-duck-ui (-1) ⊗ duckdb-ies (0) ⊗ free-monad-gen (+1) = 0 ✓
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
