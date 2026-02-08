---
name: kan-extensions
description: Kan Extensions Skill (ERGODIC 0)
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Kan Extensions Skill (ERGODIC 0)

> Universal schema migration via left/right Kan extensions

**Trit**: 0 (ERGODIC)  
**Color**: #26D826 (Green)  
**Role**: Coordinator/Transporter

## Core Concept

Kan extensions are the "best approximation" to extending a functor along another:

```
       F
   C ────→ D
   │       ↑
 K │       │ Lan_K F  (left Kan extension)
   ↓       │ Ran_K F  (right Kan extension)
   C'
```

**Adjunction**: `Lan_K ⊣ Res_K ⊣ Ran_K`

## Pointwise Formulas

### Left Kan Extension (Forward Migration)
```
(Lan_K F)(d) = colim_{(c,f: K(c)→d)} F(c)
```
- **Colimit over comma category** (K ↓ d)
- **Extends F forward** along K
- **Preserves colimits** when F does

### Right Kan Extension (Backward Migration)
```
(Ran_K F)(d) = lim_{(c,f: d→K(c))} F(c)
```
- **Limit over comma category** (d ↓ K)
- **Extends F backward** along K
- **Preserves limits** when F does

## Integration with ACSets

```julia
using Catlab, DataMigrations

# Schema migration via Kan extension
# K: SchemaOld → SchemaNew
# F: SchemaOld → Set (instance)
# Lan_K F: SchemaNew → Set (migrated instance)

function left_kan_migrate(K::DataMigration, instance::ACSet)
    # Compute colimit for each new object
    return colimit_representables(K, instance)
end

function right_kan_migrate(K::DataMigration, instance::ACSet)
    # Compute limit for each new object
    return limit_representables(K, instance)
end
```

## Schema Transport Patterns

### Pattern 1: Forward Schema Evolution
```julia
@migration SchemaV1 SchemaV2 begin
    # Lan extends forward
    NewTable => @join begin
        old::OldTable
        # computed from old structure
    end
end
```

### Pattern 2: Backward Compatibility
```julia
@migration SchemaV2 SchemaV1 begin
    # Ran projects backward
    OldTable => @join begin
        new::NewTable
        # projected from new structure
    end
end
```

### Pattern 3: Universal Property
```
For any H: C' → D with natural transformation α: F → H ∘ K
∃! β: Lan_K F → H such that 