---
name: pijul-sparse-skills
description: Sparsity-preserving skill versioning via Pijul patches with GF(3) projection gates
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# pijul-sparse-skills

Sparsity-preserving skill versioning where changes are stored as morphisms, not materialized states.

**Trit**: 0 (ERGODIC) - Coordinator role for projection gate decisions

---

## Philosophy

### Default: SPARSE Mode

```
┌─────────────────────────────────────────────────────────┐
│  SPARSE (default)                                       │
│  - Changes stored as patches (morphisms)                │
│  - No materialization unless required                   │
│  - Lazy evaluation of skill state                       │
│  - Minimal storage footprint                            │
└─────────────────────────────────────────────────────────┘
```

### Projection Only When:

| Trigger | Description | GF(3) |
|---------|-------------|-------|
| `--materialize` | Explicit flag | Any |
| `trit == 0` | ERGODIC coordination point | 0 |
| `--archive` | Explicit archive | Any |
| Conflict | Resolution requires full state | Any |

---

## Categorical Foundation

### Patches as Morphisms in Cat(Skills)

```
Ob(C) = { skill states }
Mor(C) = { patches transforming states }

For patches p, q:
  p ⊥ q (independent) ⟹ p;q = q;p (commute)
```

### Sparsity via Lazy Evaluation

```julia
# Sparse representation (default)
struct SparseSkill
    base_hash::UInt64      # Root state reference
    patches::Vector{Patch}  # Morphism chain, not applied
end

# Materialized only on demand
function materialize(s::SparseSkill)
    foldl(apply, s.patches; init=load(s.base_hash))
end
```

---

## GF(3) Projection Gates

### Gate Logic

```julia
function should_project(skill::Skill, flags::Flags)::Bool
    # Explicit materialization requested
    flags.materialize && return true
    
    # ERGODIC trit forces coordination checkpoint
    skill.trit == 0 && return true
    
    # Explicit archive
    flags.archive && return true
    
    # Conflict requires full state
    has_conflicts(skill) && return true
    
    # Otherwise: stay sparse
    return false
end
```

### Trit-Based B