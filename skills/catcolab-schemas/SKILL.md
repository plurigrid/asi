---
name: catcolab-schemas
description: CatColab Schemas - database schema modeling distinguishing entities (tables) from attributes (columns). Foundation for ACSets (Attributed C-Sets) and AlgebraicJulia data structures.
version: 1.0.0
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

## CatColab Implementation

### Entity Declaration

```typescript
{
  "type": "ObDecl",
  "name": "Person",
  "theory_type": "Entity",
  "description": "people in the system"
}
```

### Attribute Type Declaration

```typescript
{
  "type": "ObDecl",
  "name": "String",
  "theory_type": "AttrType",
  "description": "text values"
}
```

### Mapping (Foreign Key)

```typescript
{
  "type": "MorDecl",
  "name": "employer",
  "dom": "Person",
  "cod": "Company",
  "theory_type": "Mapping",
  "description": "the company this person works for"
}
```

### Attribute (Column)

```typescript
{
  "type": "MorDecl",
  "name": "salary",
  "dom": "Person",
  "cod": "Int",
  "theory_type": "Attr",
  "description": "annual salary in dollars"
}
```

## ACSet Connection

A CatColab schema defines the type; an **ACSet** is an instance:

```julia
# Schema defines structure
@present SchPerson(FreeSchema) begin
  Person::Ob
  Company::Ob

  employer::Hom(Person, Company)

  Name::AttrType
  name::Attr(Person, Name)
end

# ACSet populates data
people = @acset SchPerson begin
  Person = 3
  Company = 2
  employer = [1, 1, 2]
  name = ["Alice", "Bob", "Charlie"]
end
```

## Practical Examples

### Example 1: E-Commerce Schema

```
Entities: Customer, Order, Product, Category
AttrTypes: String, Int, Float, DateTime

Mappings:
  placed_by: Order → Customer
  contains: Order → Product (many-to-many via junction)
  in_category: Product → Category

Attributes:
  email: Customer → String
  total: Order → Float
  price: Product → Float
  name: Category → String
```

### Example 2: Social Network

```
Entities: User, Post, Comment, Group
AttrTypes: String, DateTime, Int

Mappings:
  author: Post → User
  on_post: Comment → Post
  member_of: User → Group

Attributes:
  username: User → String
  content: Post → String
  timestamp: Post → DateTime
  likes: Post → Int
```

## Schema Composition

Schemas compose via **pullback** and **pushout**:

```
     Schema A          Schema B
         \               /
          \   pullback  /
           \           /
            ▼         ▼
          Schema A ×_C B
```

## GF(3) Triads

```
catcolab-ologs (-1) ⊗ topos-catcolab (0) ⊗ catcolab-schemas (+1) = 0 ✓
database-design (-1) ⊗ acsets-relational-thinking (0) ⊗ catcolab-schemas (+1) = 0 ✓
```

## Commands

```bash
# Create schema
just catcolab-new schema "my-database"

# Generate Julia ACSet code
just catcolab-export my-database --format=julia

# Create instance (diagram)
just catcolab-instance my-database "sample-data"

# Migrate schema
just catcolab-migrate old-schema new-schema
```

## References

- Patterson et al. "Categorical data structures for technical computing" (2022)
- [AlgebraicJulia ACSets](https://algebraicjulia.github.io/ACSets.jl/)
- [CatColab Schema Help](https://catcolab.org/help/logics/schema)

---

**Skill Name**: catcolab-schemas
**Type**: Database Schema Design
**Trit**: +1 (PLUS)
**GF(3)**: Conserved via triadic composition
