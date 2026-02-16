# duckdb-guard

**Trit**: 0 (ERGODIC - coordination role)
**Seed**: 137508

Pre-query schema validation for DuckDB to prevent column-not-found errors, constraint violations, and unsafe INSERT patterns.

## Anti-Patterns Addressed

| Pattern | Count | Prevention |
|---------|-------|------------|
| Schema Mismatch (column not found) | 7 | Pre-query validation with suggestions |
| Constraint Violation (NOT NULL) | 5 | Constraint check before INSERT |
| INSERT OR IGNORE no constraints | 3 | Explicit ON CONFLICT handling |

## Usage

```python
from duckdb_guard import validate_schema, safe_insert, describe_table

# Validate before query
result = validate_schema("data.duckdb", "threads", ["id", "colour", "timestamp"])
if not result["valid"]:
    print(f"Missing: {result['missing']}, Try: {result['suggestions']}")

# Safe INSERT with auto-correction
safe_insert("data.duckdb", "threads", {
    "id": 1,
    "colour": "#8169DC",  # Will suggest 'color' if column is 'color'
    "timestamp": "2025-12-29"
}, on_conflict="REPLACE")
```

## Babashka Integration

```clojure
(require '[babashka.process :refer [shell]])

(defn validate-schema [db-path table columns]
  "Pre-flight schema validation"
  (let [result (shell {:out :string}
                 "python3" "-c" 
                 (format "from duckdb_guard import validate_schema; import json; print(json.dumps(validate_schema('%s', '%s', %s)))"
                         db-path table (pr-str columns)))]
    (json/parse-string (:out result) true)))

(defn safe-query [db-path sql]
  "Execute query only after schema validation"
  (let [tables (extract-tables sql)
        columns (extract-columns sql)]
    (doseq [t tables]
      (let [v (validate-schema db-path t columns)]
        (when-not (:valid v)
          (throw (ex-info "Schema mismatch" v)))))
    (shell {:out :string} "duckdb" db-path "-json" "-c" sql)))
```

## Core Module

See `duckdb_guard.py` for implementation with:
- `validate_schema(db_path, table, columns)` - Check columns exist
- `safe_insert(db_path, table, data, on_conflict)` - Safe INSERT
- `describe_table(db_path, table)` - Get full schema info
- `check_constraints(db_path, table)` - List NOT NULL and CHECK constraints
- `levenshtein(s1, s2)` - String similarity for suggestions

## Ruler Integration

```toml
[skills.duckdb-guard]
enabled = true
trit = 0
description = "Schema validation before queries"
propagate = ["claude", "codex", "amp"]
```

## Autopoiesis Integration

Add to system prompts:
```
## DuckDB Safety
- Always validate schema before INSERT/UPDATE
- Use explicit column lists, never INSERT *
- Check constraints before INSERT OR IGNORE
- Use safe_insert() with on_conflict handling
```

## GF(3) Conservation

This skill has trit=0 (ERGODIC), coordinating between:
- `duckdb-temporal-versioning` (existing)
- `duckdb-ies` (existing)  
- `timeout-batcher` (trit=+1, to be created)

## Dependencies

- Python 3.9+ with duckdb
- Optional: babashka for Clojure integration


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
