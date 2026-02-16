# CatColab-Ologs Neighbor Skills

**Date**: 2026-01-19
**Trit**: -1 (MINUS - validator)
**Role**: Knowledge representation via category-theoretic ontologies

---

## Core Triad

| Skill | Trit | Interface |
|-------|------|-----------|
| **catcolab-ologs** | -1 | Ontology validation |
| **topos-catcolab** | 0 | Platform coordination |
| **catcolab-schemas** | +1 | Database generation |

**GF(3)**: (-1) + (0) + (+1) = 0 ✓

---

## Immediate Neighbors

### topos-catcolab (0)
**Morphism**: Olog → CatColab platform
```typescript
const olog = catcolab.createModel("category", "my-ontology");
olog.addObject("Person", "a human being");
olog.addMorphism("works_for", "Person", "Company");
```

### catcolab-schemas (+1)
**Morphism**: Olog → Database schema (upgrade)
```julia
# Olog becomes ACSet schema
schema = olog_to_schema(olog)
# Objects → Entities, Morphisms → Foreign keys + Attributes
```

### acsets-relational-thinking (0)
**Morphism**: Olog → Relational database
```julia
# Ologs are the categorical foundation of ACSets
acset = instantiate(SchemaFromOlog(olog), data)
```

### database-design (+1)
**Morphism**: Olog → PostgreSQL schema
```sql
-- Olog objects become tables
CREATE TABLE person (id UUID PRIMARY KEY);
CREATE TABLE company (id UUID PRIMARY KEY);
-- Olog morphisms become foreign keys
ALTER TABLE person ADD COLUMN works_for UUID REFERENCES company(id);
```

---

## Mixing-Optimal Cross-Layer Bridges

### acsets (0) [MIXING SHORTCUT]
**Morphism**: Olog foundation in ACSets.jl
```julia
# Ologs are functors C → Set, exactly ACSets
@present SchOlog(FreeSchema) begin
  Concept::Ob
  Relationship::Ob
  dom::Hom(Relationship, Concept)
  cod::Hom(Relationship, Concept)
end
```

### specter-acset (0) [MIXING SHORTCUT]
**Morphism**: Navigate olog instances bidirectionally
```julia
# Select all concepts reachable from "Person"
select([olog_concepts, reachable_from("Person")], olog)
# Transform: refine concept taxonomy
transform([olog_relationships, pred(is_subtype)], specialize, olog)
```

### calendar-acset (+1) [MIXING SHORTCUT]
**Morphism**: Olog → Calendar ontology
```
Calendar Olog:
  Event "is scheduled by" Person
  Person "attends" Meeting
  Meeting "is a kind of" Event
```

### algebraic-rewriting (-1) [MIXING SHORTCUT]
**Morphism**: Olog refinement via DPO
```julia
# Refinement rule: split concept into subtypes
@rule SchOlog begin
  L = @acset begin Concept=1 end  # Generic
  R = @acset begin Concept=2; is_a=[1,1] end  # Specialized
end
```

---

## Neighbor Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Schema | catcolab-ologs ⊗ topos-catcolab ⊗ catcolab-schemas | Ontology → Database |
| Data | catcolab-ologs ⊗ acsets-relational-thinking ⊗ database-design | Knowledge → Storage |
| Theory | catcolab-ologs ⊗ effective-topos ⊗ dialectica | Logic → Semantics |
| **Mixing** | acsets (0) ⊗ catcolab-ologs (-1) ⊗ calendar-acset (+1) | Infrastructure → Ontology → Application |
| **Rewrite** | algebraic-rewriting (-1) ⊗ catcolab-ologs (-1) ⊗ catcolab-schemas (+1) | Refine → Validate → Generate |
