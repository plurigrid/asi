---
name: behaviour-surprisal-analysis
description: Behaviour Surprisal Analysis
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Behaviour Surprisal Analysis

**Status**: Production Ready (v3.0 - Cat# Integration)
**Trit**: 0 (ERGODIC - measurement/observation)
**Principle**: S(x) = -log₂(P(x|attention_mode))
**Frame**: Tri-channel prediction evaluation with AGM belief revision + Cat# bicomodule structure

---

## Overview

**Behaviour Surprisal Analysis** calculates information-theoretic surprise between predictions and observed outcomes using three complementary attention channels mapped to Cat# = Comod(P) structure:

| Channel | Trit | Home | Poly Op | Kan Role | Description |
|---------|------|------|---------|----------|-------------|
| **Direct** (α) | −1 | Span | × (product) | Ran_K | Exact artifact matching |
| **Diffuse** (β) | 0 | Prof | ⊗ (parallel) | Adj | Thematic/structural matching |
| **Meta** (γ) | +1 | Presheaves | ◁ (substitution) | Lan_K | Capability/infrastructure tracking |

```
Total Surprisal = α·S_direct + β·S_diffuse + γ·S_meta
where α + β + γ = 1 and typically α=0.3, β=0.5, γ=0.2
```



## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 5. Evaluation

**Concepts**: eval, apply, interpreter, environment

### GF(3) Balanced Triad

```
behaviour-surprisal-analysis (−) + SDF.Ch5 (−) + [balancer] (−) = 0
```

**Skill Trit**: -1 (MINUS - verification)

### Secondary Chapters

- Ch1: Flexibility through Abstraction
- Ch4: Pattern Matching
- Ch6: Layering
- Ch10: Adventure Game Example

### Connection Pattern

Evaluation interprets expressions. This skill processes or generates evaluable forms.
## Cat# Integration (v3.0)

### Galois Adjunction α ⊣ γ

The Direct and Meta channels form a Galois adjunction through the Diffuse bridge:

```
         α (abstract)
  Direct ─────────────→ Diffuse
    ↑                      │
    │        CatSharp      │ γ (concretize)
    │         Scale        │
    └──────────────────────┘
           Meta

  GF(3): (−1) + (0) + (+1) = 0 ✓
```

- **α (abstraction)**: Di