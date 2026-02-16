# GAY.md - Color Assignment

```
Skill: data-science-cli
Color: #2518AA
Trit: -1 (MINUS/Validator)
Hash: 79b669340850382d
URI: skill://data-science-cli#2518AA
```

## Filesystem Change Color Mapping

| Change Type | Hex | Trit | Retrieval Key |
|-------------|-----|------|---------------|
| CREATE | #C44955 | +1 | `fs:create` |
| MODIFY | #16C061 | 0 | `fs:modify` |
| DELETE | #2518AA | -1 | `fs:delete` |
| RENAME | #16C061 | 0 | `fs:rename` |
| CHMOD | #16C061 | 0 | `fs:chmod` |

## DuckDB Schema for Color-Indexed FS Changes

```sql
CREATE TABLE fs_changes (
  id INTEGER PRIMARY KEY,
  timestamp TIMESTAMP DEFAULT now(),
  path VARCHAR,
  operation VARCHAR,  -- create/modify/delete/rename/chmod
  hex VARCHAR(7),     -- Gay.jl color
  trit TINYINT,       -- -1, 0, +1
  seed UBIGINT DEFAULT 69
);

CREATE INDEX idx_trit ON fs_changes(trit);
CREATE INDEX idx_hex ON fs_changes(hex);
```

## Query by Color

```sql
-- All creations (warm)
SELECT * FROM fs_changes WHERE trit = 1;

-- All deletions (cold)  
SELECT * FROM fs_changes WHERE trit = -1;

-- GF(3) conservation check
SELECT SUM(trit) % 3 AS balance FROM fs_changes;
```
