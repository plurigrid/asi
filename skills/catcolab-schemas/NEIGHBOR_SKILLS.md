# CatColab-Schemas Neighbor Skills

**Date**: 2026-01-19
**Trit**: +1 (PLUS - generator)
**Role**: Database schema generation from categorical specifications

---

## Core Triad

| Skill | Trit | Interface |
|-------|------|-----------|
| **catcolab-ologs** | -1 | Ontology foundation |
| **topos-catcolab** | 0 | Platform coordination |
| **catcolab-schemas** | +1 | Schema generation |

**GF(3)**: (-1) + (0) + (+1) = 0 ✓

---

## Immediate Neighbors

### topos-catcolab (0)
**Morphism**: Schema → CatColab model
```typescript
const schema = catcolab.createModel("schema", "ecommerce");
schema.addEntity("Customer");
schema.addEntity("Order");
schema.addMapping("placed_by", "Order", "Customer");
schema.addAttr("email", "Customer", "String");
```

### catcolab-ologs (-1)
**Morphism**: Olog → Schema (upgrade)
```
Olog (conceptual)  →  Schema (typed)
  Object: Person   →    Entity: Person + AttrType: String
  Morphism: name   →    Attr: name: Person → String
```

### acsets-relational-thinking (0)
**Morphism**: Schema → ACSet instance
```julia
@present SchCustomer(FreeSchema) begin
  Customer::Ob; Order::Ob
  placed_by::Hom(Order, Customer)
  Name::AttrType
  name::Attr(Customer, Name)
end

customers = @acset SchCustomer begin
  Customer = 2; Order = 3
  placed_by = [1, 1, 2]
  name = ["Alice", "Bob"]
end
```

### database-design (+1)
**Morphism**: Schema → SQL DDL
```sql
-- Generated from CatColab schema
CREATE TABLE customer (
  id UUID PRIMARY KEY,
  name VARCHAR NOT NULL
);
CREATE TABLE "order" (
  id UUID PRIMARY KEY,
  placed_by UUID REFERENCES customer(id)
);
```

---

## ACSet Infrastructure Bridges

### acsets (0)
**Morphism**: Double theory → @acset_type
```julia
# CatColab schema ↔ ACSets.jl
@acset_type CustomerDB(SchCustomer, index=[:placed_by])
```

### specter-acset (0)
**Morphism**: Navigate schema instances bidirectionally
```julia
select([acset_parts(:Order), acset_field(:placed_by)], db)
transform([acset_where(:Customer, :name, ==("Alice"))], promote, db)
```

### algebraic-rewriting (-1)
**Morphism**: Schema evolution via DPO rewriting
```julia
# Add required attribute to entity
@rule SchSchema begin
  L = @acset begin e::Entity end
  R = @acset begin e::Entity; a::Attribute; entity_attr(a)==e end
end
```

---

## Neighbor Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Data | catcolab-ologs ⊗ catcolab-schemas ⊗ database-design | Concept → Schema → DDL |
| ACSet | catcolab-schemas ⊗ acsets-relational-thinking ⊗ specter-acset | Schema → Instance → Navigation |
| Migration | catcolab-schemas ⊗ topos-catcolab ⊗ covariant-modification | Schema evolution |
| **Cross-layer** | acsets (0) ⊗ catcolab-schemas (+1) ⊗ tasks-acset (-1) | Infra → Modeling → App |
| **Deep** | algebraic-rewriting (-1) ⊗ catcolab-schemas (+1) ⊗ gmail-anima (0) | Rewrite → Schema → Email |
