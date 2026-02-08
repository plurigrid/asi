---
name: catcolab-schemas
description: CatColab Schemas - database schema modeling distinguishing entities (tables) from attributes (columns). Foundation for ACSets (Attributed C-Sets) and AlgebraicJulia data structures.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# CatColab Schemas: Database Schema Modeling

**Trit**: +1 (PLUS - generator)
**Color**: Green (#32CD32)

## Overview

Schemas in CatColab upgrade ologs by explicitly distinguishing:
- **Entities**: Tables with identity (foreign key targets)
- **Attributes**: Columns/properties (data values)
- **Mappings**: Foreign key relationships

This is the foundation for **ACSets** (Attributed C-Sets), the core data structure of AlgebraicJulia.

## Mathematical Foundation

A schema is a **profunctor** or displayed category:

```
┌─────────────────────────────────────────────────────┐
│                     SCHEMA                           │
├─────────────────────────────────────────────────────┤
│  Entities (Ob):                                      │
│    Person, Company, Project                          │
│                                                      │
│  AttrTypes (Data):                                   │
│    String, Int, Date, Bool                           │
│                                                      │
│  Mappings (Hom):                                     │
│    works_at: Person → Company                        │
│    leads: Person → Project                           │
│                                                      │
│  Attributes (Attr):                                  │
│    name: Person → String                             │
│    age: Person → Int                                 │
│    founded: Company → Date                           │
└─────────────────────────────────────────────────────┘
```

## Double Theory

```rust
// Schema double theory in catlog
pub fn th_schema() -> DiscreteDblTheory {
    let mut cat = FpCategory::new();

    // Object types
    cat.add_ob_generator(name("Entity"));
    cat.add_ob_generator(name("AttrType"));

    // Morphism types
    cat.add_mor_generator(name("Mapping"), name("Entity"), name("Entity"));
    cat.add_mor_generator(name("Attr"), name("Entity"), name("AttrType"));

    cat.into()
}
```

## Ca