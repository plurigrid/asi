# py-acsets vs ACSets.jl: Semantic & Syntactic Discrepancies

## Source Analysis
- **Python**: AlgebraicJulia/py-acsets (cloned to `/Users/bob/iii/py-acsets`)
- **Julia**: ACSets.jl v0.2.26

---

## API Comparison Matrix

### Core Operations

| Operation | Julia (ACSets.jl) | Python (py-acsets) | Discrepancy |
|-----------|-------------------|-------------------|-------------|
| Add single row | `add_part!(acs, :V)` | `acs.add_part("V")` | ✅ Compatible |
| Add multiple rows | `add_parts!(acs, :V, n)` | `acs.add_parts("V", n)` | ✅ Compatible |
| Get row count | `nparts(acs, :V)` | `acs.nparts(Ob("V"))` | ⚠️ Python requires Ob wrapper |
| Get row range | `parts(acs, :V)` | `acs.parts(Ob("V"))` | ⚠️ Python requires Ob wrapper |
| Get subpart | `subpart(acs, i, :src)` | `acs.subpart(i, Hom(...))` | ❌ Python requires full Hom/Attr object |
| Set subpart | `set_subpart!(acs, i, :src, v)` | `acs.set_subpart(i, Hom(...), v)` | ❌ Python requires full Hom/Attr object |
| Check subpart | `has_subpart(acs, :src)` | `acs.has_subpart(i, Hom(...))` | ❌ Different semantics |
| Incident query | `incident(acs, v, :src)` | `acs.incident(v, Hom(...))` | ❌ Python requires full Hom object |
| Remove part | `rem_part!(acs, :V, i)` | ❌ **NOT IMPLEMENTED** | 🔴 **MISSING** |
| Remove parts | `rem_parts!(acs, :V, range)` | ❌ **NOT IMPLEMENTED** | 🔴 **MISSING** |
| Cascading remove | `cascading_rem_part!(acs, :V, i)` | ❌ **NOT IMPLEMENTED** | 🔴 **MISSING** |
| Copy parts | `copy_parts!(acs1, acs2)` | ❌ **NOT IMPLEMENTED** | 🔴 **MISSING** |
| Clear subpart | `clear_subpart!(acs, i, :src)` | ✅ via `set_subpart(i, f, None)` | ✅ Compatible |
| GC deleted | `gc!(acs)` | ❌ **NOT IMPLEMENTED** | 🔴 **MISSING** |

### Schema Operations

| Operation | Julia | Python | Discrepancy |
|-----------|-------|--------|-------------|
| Define schema | `@present SchGraph...` | `Schema.from_catlab(...)` | Different DSL |
| Get objects | `objects(schema)` | `schema.obs` | Property vs function |
| Get morphisms | `homs(schema)` | `schema.homs` | Property vs function |
| Get attributes | `attrs(schema)` | `schema.attrs` | Property vs function |
| Get attr types | `attrtypes(schema)` | `schema.attrtypes` | Property vs function |
| Domain | `dom(hom)` | `hom.dom` | Property vs function |
| Codomain | `codom(hom)` | `hom.codom` | Property vs function |

### Serialization

| Operation | Julia | Python | Discrepancy |
|-----------|-------|--------|-------------|
| To JSON | `generate_json_acset(acs)` | `acs.to_json_obj()` | ✅ Compatible format |
| From JSON | `parse_json_acset(schema, json)` | `ACSet.from_obj(name=..., obj=...)` | ✅ Compatible |
| Write file | `write_json_acset(acs, path)` | `acs.to_json_file(path)` | ✅ Compatible |
| Read file | `read_json_acset(schema, path)` | `ACSet.from_file(name=..., path=...)` | ⚠️ Python requires name |
| Pydantic export | ❌ | `acs.export_pydantic()` | Python-only feature |
| Pydantic import | ❌ | `acs.import_pydantic(model)` | Python-only feature |

### Advanced Features

| Feature | Julia | Python | Status |
|---------|-------|--------|--------|
| Nauty isomorphism | ✅ `call_nauty()` | ❌ | 🔴 MISSING |
| Excel I/O | ✅ `read_xlsx_acset()` | ❌ | 🔴 MISSING |
| Query DSL | ✅ `Query`, `Select`, `Where` | ❌ | 🔴 MISSING |
| Type-level schema | ✅ `TypeLevelSchema` | ❌ | 🔴 MISSING |
| Struct ACSets | ✅ `StructACSet` | ❌ | 🔴 MISSING |
| Attribute variables | ✅ `AttrVar` | ❌ | 🔴 MISSING |
| Disjoint union | ✅ `disjoint_union()` | ❌ | 🔴 MISSING |
| Densify/Sparsify | ✅ `densify()`, `sparsify()` | ❌ | 🔴 MISSING |

---

## Syntactic Differences

### 1. Symbol vs String for Table Names

```julia
# Julia - uses symbols
add_part!(acs, :V)
nparts(acs, :V)
```

```python
# Python - uses strings (or Ob objects)
acs.add_part("V")
acs.nparts(Ob("V"))
```

**Impact**: Minor - Python allows both strings and Ob objects.

### 2. Property Access Style

```julia
# Julia - function-based
subpart(acs, 1, :src)
```

```python
# Python - requires Hom/Attr object
src_hom = Hom(name="src", dom="E", codom="V")
acs.subpart(1, src_hom)
```

**Impact**: Major - Python is more verbose, less ergonomic.

### 3. Schema Definition

```julia
# Julia - macro DSL
@present SchGraph(FreeSchema) begin
    V::Ob
    E::Ob
    src::Hom(E, V)
    tgt::Hom(E, V)
end
```

```python
# Python - JSON/Catlab format
catlab_schema = {
    "Ob": [{"name": "V"}, {"name": "E"}],
    "Hom": [
        {"name": "src", "dom": "E", "codom": "V"},
        {"name": "tgt", "dom": "E", "codom": "V"}
    ]
}
schema = Schema.from_catlab(name="Graph", catlab_schema=catlab_schema)
```

**Impact**: Major - Julia has much more ergonomic schema definition.

---

## Semantic Differences

### 1. Indexing

| Aspect | Julia | Python |
|--------|-------|--------|
| Default | 1-indexed | 0-indexed |
| Optional | N/A | `oneindex=True` parameter |

### 2. Mutability Convention

```julia
# Julia - bang suffix for mutation
add_part!(acs, :V)  # mutates
set_subpart!(acs, 1, :src, 2)  # mutates
```

```python
# Python - no suffix (always mutates)
acs.add_part("V")  # mutates
acs.set_subpart(1, hom, 2)  # mutates
```

### 3. Return Values

| Operation | Julia Return | Python Return |
|-----------|--------------|---------------|
| `add_part!` | `Int` (1-indexed) | `int` (0-indexed) |
| `add_parts!` | `UnitRange` | `range` |
| `nparts` | `Int` | `int` |
| `parts` | `OneTo` | `range` |

---

## Missing in Python (Priority Order)

### P0 - Critical
1. `rem_part!` / `rem_parts!` - Cannot delete rows
2. `cascading_rem_part!` - No referential integrity on delete

### P1 - Important
3. Query DSL (`Select`, `Where`, `From`)
4. `copy_parts!` - Cannot copy between ACSets
5. `disjoint_union` - Cannot combine ACSets

### P2 - Nice to Have
6. Nauty isomorphism checking
7. Excel I/O
8. Attribute variables
9. Struct ACSets (performance optimization)

---

## Python-Only Features

1. **Pydantic integration** - `export_pydantic()`, `import_pydantic()`
2. **JSON Schema generation** - Can generate JSON Schema for validation

---

## Recommendations for py-acset Skill

### Immediate Improvements
1. Add name-based lookup for subparts: `acs.subpart(i, "src")` 
2. Implement `rem_part!` equivalent
3. Add helper for schema definition from dict

### GF(3) Integration Points
```python
# Trit assignment for ACSet operations
TRIT_MAP = {
    'add_part': +1,    # PLUS: generation
    'set_subpart': 0,  # ERGODIC: coordination
    'rem_part': -1,    # MINUS: validation/cleanup
}
```

### Ollama Action Space Schema (proposed extension)
```python
from acsets import Schema, ACSet

# Use official py-acsets as base, extend with Ollama schema
ollama_schema = Schema.from_catlab(
    name="OllamaActionSpace",
    catlab_schema={
        "Ob": [
            {"name": "Model"},
            {"name": "Request"},
            {"name": "Response"},
            {"name": "Runner"}
        ],
        "Hom": [
            {"name": "request_model", "dom": "Request", "codom": "Model"},
            {"name": "response_request", "dom": "Response", "codom": "Request"},
            {"name": "runner_model", "dom": "Runner", "codom": "Model"}
        ],
        "AttrType": [
            {"name": "String", "ty": "str"},
            {"name": "Int", "ty": "int"},
            {"name": "Bool", "ty": "bool"}
        ],
        "Attr": [
            {"name": "model_name", "dom": "Model", "codom": "String"},
            {"name": "request_prompt", "dom": "Request", "codom": "String"},
            {"name": "request_trit", "dom": "Request", "codom": "Int"},
            {"name": "response_chunk", "dom": "Response", "codom": "String"}
        ]
    }
)
```
