---
name: coequalizers
description: Quotient redundant skill paths via coequalizers, preserving GF(3) conservation
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Coequalizers Skill

> **Quotient redundant skill paths via categorical coequalizers**

**Version**: 1.0.0  
**Trit**: 0 (ERGODIC - coordinates equivalences)  
**Domain**: category-theory, skill-composition, colimits, behavioral-equivalence

---

## Overview

The **coequalizers** skill provides:

1. **Behavioral equivalence checking** via bisimulation (from temporal-coalgebra)
2. **Parallel morphism quotienting** via coequalizers (colimits)
3. **Skill overlap detection** and gluing (from oapply-colimit pushouts)
4. **GF(3) conservation** in quotient spaces
5. **MCP integration** for cross-agent skill synchronization

---

## Core Concept

### What Are Coequalizers?

A **coequalizer** is the colimit of two parallel morphisms:

```
    X ──f──→ Y
    │  g     │
    └────────→ q
             ↓
             Q  (coequalizer)

Universal property: q ∘ f = q ∘ g
```

**In Sets**: Q = Y / ~ where ~ is the smallest equivalence relation such that f(x) ~ g(x) for all x ∈ X.

**For skills**: If two skill paths produce behaviorally equivalent outputs, the coequalizer gives the canonical quotient.

---

## Key Patterns from asi Repository

### 1. oapply-colimit: Pushout = Coproduct + Coequalizer

From `/skills/oapply-colimit/SKILL.md`:

```julia
function oapply(d::UndirectedWiringDiagram, xs::Vector{ResourceSharer})
    # Step 1: Coproduct of state spaces
    S = coproduct((FinSet ∘ nstates).(xs))
    
    # Step 2: Pushout identifies shared variables via COEQUALIZER
    S′ = pushout(portmap, junctions)  # ← Uses coequalizer internally
    
    # Step 3: Induced dynamics sum at junctions
    return ResourceSharer(induced_interface, induced_dynamics)
end
```

**Key insight**: Pushouts decompose as coproduct + coequalizer. This is how skills with **shared interfaces** are glued together.

### 2. Bisimulation-game: Behavioral Equivalence

From `/skills/bisimulation-game/SKILL.md`:

```python
def bisimilar(skill₁, skill₂, input, depth=10):
    """
    Recursively check if skills prod