---
name: relational-thinking
description: Intent taxonomy and morphisms across 15 amp threads
trit: 0
probe: "bb -e '(println \"6 intents × 15 threads × 18 morphisms = GF(3) balanced\")'"
---

# Relational Thinking Skill

> *"Structure is the invariant under transformation."*

## Overview

This skill provides a **relational thinking structure** that organizes 15 amp threads into 6 intent clusters with explicit morphisms between them. All clusters maintain GF(3) conservation.

## Intent Clusters

| Cluster | Trit | Threads | Key Bridge |
|---------|------|---------|------------|
| Triadic Algebra | -1 | 3 | SHA3 ↔ GF(3) ↔ PlusCode |
| Skill Orchestration | 0 | 3 | 443 skills ↔ OSIS ↔ triplets |
| Energy Policy | +1 | 2 | SMR ↔ Plurigrid ↔ dominance |
| Topological ASI | 0 | 2 | 26 worlds ↔ Unworld ↔ Narya |
| System Introspection | -1 | 2 | PID ↔ radare2 ↔ process |
| Implementation | +1 | 3 | Zig ↔ MCP ↔ wallet |

## GF(3) Triads

```
Core:  Triadic(-1) ⊗ Skill(0) ⊗ Energy(+1) = 0
Meta:  System(-1) ⊗ Topo(0) ⊗ Impl(+1) = 0
```

## Thread Mapping

### Triadic Algebra (-1)
- `amp-thread-sha3-conversion-gf3-conservation.md` (148 msg)
- `amp-thread-gf3-geographic-ripple-repl.md` (79 msg)
- `amp-thread-prime-length-plus-code-frontrun.md` (151 msg)

### Skill Orchestration (0)
- `amp-thread-skill-orchestration-framework.md` (51 msg)
- `amp-thread-skill-analysis-ssh-hatchery.md` (123 msg)
- `amp-thread-push-skills-enable-uv-uvx.md` (19 msg)

### Energy Policy (+1)
- `amp-thread-energy-dominance-agenda-synthesis.md` (70 msg)
- `amp-thread-energy-dominance-co-occurring.md` (35 msg)

### Topological ASI (0)
- `amp-thread-topological-superintelligence-readme.md` (144 msg)
- `amp-thread-find-aptos-society-zubyul.md` (115 msg)

### System Introspection (-1)
- `amp-thread-locate-process-in-parent-pid-tree.md` (47 msg)
- `amp-thread-find-process-in-pid-tree-with-parent.md` (102 msg)

### Implementation (+1)
- `amp-thread-zig-benchmark-compilation-error.md` (94 msg)
- `amp-thread-mcps-per-letter-wallet-count.md` (149 msg)
- `amp-thread-zubyul-skill-implementation.md` (24 msg)

## Morphism Types

| Type | Description | Example |
|------|-------------|---------|
| `composition` | A → B → C | SHA3 → Geographic → PlusCode |
| `bridge` | Cross-cluster | Triadic → Skill (balance constraint) |
| `reflection` | Self-loop | Zubyul ↔ Zubyul (implementation feedback) |
| `adjunction` | Free/Forgetful | Energy ⊣ Policy |

## Usage

### Query Cluster
```bash
# Find threads in a cluster
grep -l "GF(3)" ~/amp-thread-*.md

# Count by intent
ls ~/amp-thread-*.md | wc -l  # 15
```

### Load into DuckDB
```sql
ATTACH '~/relational_thinking.duckdb' AS rt;

CREATE TABLE rt.clusters AS
SELECT * FROM read_csv_auto('~/relational-thinking-skill-structure.md');
```

### Navigate Morphisms
```clojure
;; Babashka navigation
(def morphisms
  {:triadic->skill :balance
   :skill->energy :coexist
   :energy->topo :smr
   :topo->system :world
   :system->impl :binary
   :impl->triadic :verify})

(defn walk-cluster [from]
  (get morphisms (keyword (str (name from) "->skill"))))
```

## Related Skills

- `triadic-skill-orchestrator` - Orchestrates skills in GF(3) triplets
- `glass-bead-game` - Interdisciplinary synthesis
- `autopoiesis` - Self-modifying configuration
- `gay-mcp` - Deterministic color generation
- `world-extractable-value` - Nash/Optimal gap quantification

## See Also

- [Full structure document](~/relational-thinking-skill-structure.md)
- [Skill co-occurrence graph](~/ies/SKILL_COOCCURRENCE_GRAPH.md)
- [Energy dominance agenda](~/ies/PLURIGRID_ENERGY_DOMINANCE_AGENDA.md)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
