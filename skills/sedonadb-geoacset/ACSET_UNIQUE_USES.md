# ACSet Unique Uses in SedonaDB-GeoACSet Bridge

**What ACSets provide that SQL alone cannot**

## 1. Schema-as-Category

**SQL**: Schema is metadata, separate from data
```sql
CREATE TABLE buildings (id INT, parcel_id INT REFERENCES parcels(id));
-- Schema is external, constraints are checked at runtime
```

**ACSet**: Schema IS the category, morphisms are first-class
```julia
@present SchSpatialCity(FreeSchema) begin
    Building::Ob
    Parcel::Ob
    building_on::Hom(Building, Parcel)  # Morphism in the category
end
# Schema defines valid compositions statically
```

**Unique value**: Compile-time verification of structural invariants

## 2. Bidirectional Traversal via Incident

**SQL**: Must write separate queries for each direction
```sql
-- Forward: building → parcel
SELECT p.* FROM parcels p WHERE p.id = (SELECT parcel_id FROM buildings WHERE id = ?);

-- Reverse: parcel → buildings  
SELECT b.* FROM buildings b WHERE b.parcel_id = ?;
```

**ACSet**: Single API for both directions
```julia
# Forward
parcel = city[building_id, :building_on]

# Reverse (automatically indexed)
buildings = incident(city, parcel_id, :building_on)
```

**Unique value**: Symmetric access pattern, automatic reverse indexing

## 3. Homomorphism Verification

**SQL**: No built-in concept of structure-preserving maps
```sql
-- Manual: check if data transformation preserves relationships
-- No standard way to verify schema compatibility
```

**ACSet**: Native homomorphism detection
```julia
# Verify map between ACsets preserves structure
h = homomorphism(city1, city2)
@assert is_natural(h)  # Checks all squares commute

# Find all structure-preserving embeddings
embeddings = homomorphisms(pattern, city)
```

**Unique value**: Pattern matching with structural guarantees

## 4. DPO Rewriting

**SQL**: UPDATE/DELETE don't preserve structural invariants
```sql
-- Dangerous: may orphan buildings
DELETE FROM parcels WHERE id = 42;
```

**ACSet**: Double Pushout preserves gluing conditions
```julia
# Safe rewrite: buildings are automatically reassigned or deleted
rewrite_match!(rule, match) do city
    # Guaranteed to maintain ACSet invariants
end
```

**Unique value**: Categorical graph rewriting with correctness guarantees

## 5. Colimit Construction (Gluing)

**SQL**: UNION doesn't preserve relationships across sources
```sql
SELECT * FROM city1.buildings
UNION
SELECT * FROM city2.buildings;
-- Foreign keys may conflict, relationships lost
```

**ACSet**: Colimit glues while preserving structure
```julia
# Glue two cities along shared boundary
merged = colimit(Span(city1 ← boundary → city2))
# All morphisms composed correctly
```

**Unique value**: Compositional assembly of complex structures

## 6. Functorial Semantics

**SQL**: Views are syntactic, not semantic
```sql
CREATE VIEW district_summary AS 
SELECT d.id, COUNT(b.id) as building_count
FROM districts d LEFT JOIN ... 
-- Just a query, no categorical meaning
```

**ACSet**: Functors map between schemas
```julia
# Functor from detailed schema to summary schema
F: SchSpatialCity → SchDistrictSummary

# Apply to data
summary = F(city)  # Preserves all categorical structure
```

**Unique value**: Schema evolution with semantic preservation

## 7. Typed Attributes with Constraints

**SQL**: Constraints are runtime checks
```sql
CREATE TABLE buildings (
    gf3_trit INT CHECK (gf3_trit IN (-1, 0, 1))
);
-- Constraint checked on each insert
```

**ACSet**: Attributes are functors to type categories
```julia
@present SchGF3City(FreeSchema) begin
    Building::Ob
    Trit::AttrType  # Maps to GF(3) type
    building_trit::Attr(Building, Trit)
    
    # Conservation law: sum over any region = 0 mod 3
    # Enforceable at schema level
end
```

**Unique value**: Type-theoretic attribute constraints

## 8. Sheaf Condition Verification

**SQL**: No concept of local-to-global consistency
```sql
-- No standard way to verify overlapping regions agree
```

**ACSet**: Sheaf conditions are checkable
```julia
# Verify data on overlapping regions is consistent
@assert is_sheaf(city, open_cover)

# Glue local data into global section
global_section = sheafify(local_data, cover)
```

**Unique value**: Local-to-global consistency for distributed data

## 9. GF(3) Conservation as Diagram Commutativity

**SQL**: Manual sum checks
```sql
SELECT CASE WHEN SUM(trit) % 3 = 0 THEN 'ok' ELSE 'fail' END FROM buildings;
```

**ACSet**: Conservation as commuting diagram
```julia
# GF(3) as functor to Z/3Z
# Conservation = diagram commutes
@assert commutes(
    buildings → trits → Z3,
    buildings → parcels → aggregate_trit → Z3
)
```

**Unique value**: Algebraic invariants as categorical structure

## 10. Span/Cospan for Bidirectional Bridges

**SQL**: Bridge tables are ad-hoc
```sql
CREATE TABLE building_tile_bridge (
    building_id INT REFERENCES buildings(id),
    tile_code VARCHAR REFERENCES tiles(code)
);
```

**ACSet**: Spans are first-class
```julia
# Span: Buildings ← BridgeApex → Tiles
# Encodes bidirectional relationship categorically
bridge = Span(
    buildings ← apex → tiles,
    left = :building_of,
    right = :tile_of
)

# Compose spans via pullback
composed = pullback(bridge1, bridge2)
```

**Unique value**: Compositional multi-way relationships

## Summary: When to Use Each

| Need | Use SQL/SedonaDB | Use ACSet |
|------|------------------|-----------|
| Fast spatial queries | ✓ | |
| KNN search | ✓ | |
| Compile-time schema verification | | ✓ |
| Bidirectional traversal | | ✓ |
| Pattern matching with structure | | ✓ |
| Safe graph rewriting | | ✓ |
| Compositional assembly | | ✓ |
| GF(3) conservation | Both | ✓ (categorical) |

**Optimal workflow**:
1. Model domain in ACSet schema (categorical semantics)
2. Export to SedonaDB for spatial queries (performance)
3. Import results back to ACSet for morphism operations
4. Verify invariants in ACSet (correctness)
