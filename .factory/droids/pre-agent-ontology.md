---
name: pre-agent-ontology
description: Pre-Agent Ontology Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Pre-Agent Ontology Skill

**Trit**: 0 (ERGODIC - coordinates the ontology)

Foundational 5-layer ontology for agent-o-rama. Agents are not primitives—they emerge from derivations, stalks, and sections when gluing succeeds.

## Related Skills
- **unworld**: Derivational succession (Layer 1)
- **sheaf-cohomology**: Gluing verification (Layer 2)
- **bisimulation-game**: Observational equivalence (Layer 2)
- **acsets**: Categorical database structure (Layer 2)

---

## 5-Layer Hierarchy

```
Layer 4: EMERGENT        agent, skill, experiment
            ↑
Layer 3: OPERATIONAL     node, emit, aggregation, result
            ↑
Layer 2: SHEAF           stalk, section, cohomology
            ↑
Layer 1: DERIVATIONAL    derivation, chain
            ↑
Layer 0: PRE-ONTOLOGICAL seed, trit, γ (gamma)
```

### Layer 0: Pre-Ontological (Absolute Primitives)

| Term | Type | Definition |
|------|------|------------|
| seed | uint64 | Deterministic state replacing time |
| trit | {-1, 0, +1} | GF(3) charge element |
| γ | constant | 0x9E3779B97F4A7C15 (golden ratio bits) |

### Layer 1: Derivational

| Term | Type | Definition |
|------|------|------------|
| derivation | (Seed × Trit) → (Seed × Section) | Fundamental computation unit |
| chain | [Seed] | Sequence of derived seeds |

**Rule**: `seed_{n+1} = splitmix64(seed_n ⊕ (trit_n × γ))`

### Layer 2: Sheaf-Theoretic

| Term | Type | Definition |
|------|------|------------|
| stalk | Set(Section) | Collection of sections over one trit |
| section | local data | Output of derivation, can glue |
| cohomology | (H⁰, H¹) | Global sections and obstructions |

**Stalk Distribution (2-3-2)**:
```
MINUS:   2 elements, trit=-1, role=validator
ERGODIC: 3 elements, trit=0,  role=coordinator
PLUS:    2 elements, trit=+1, role=generator

Verification: 2(-1) + 3(0) + 2(+1) = 0 ✓
```

### Layer 3: Operational

| Term | Sheaf Correspondence |
|------|---------------------|
| node | section-producer |
| emit | stalk transition |
| aggregation 