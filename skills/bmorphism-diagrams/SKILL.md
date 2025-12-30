# bmorphism Diagrams

Interleave bmorphism's mermaid diagrams into interactions using GF(3) triadic selection.

## Data Source

```
~/mermaid_diagrams.duckdb
├── diagrams (251 rows)
│   ├── id: UUID
│   ├── content: VARCHAR (mermaid code)
│   ├── diagram_type: VARCHAR (graph|flowchart|stateDiagram|...)
│   ├── trit: INTEGER (-1, 0, +1)
│   └── content_hash: VARCHAR
```

## Diagram Types

| Type | Count | Use Case |
|------|-------|----------|
| graph | 126 | Dependency/skill relationships |
| flowchart | 47 | Process flows, architectures |
| stateDiagram | 8 | State machines, protocols |
| sequenceDiagram | 6 | Message passing, APIs |
| classDiagram | 6 | Type hierarchies |
| pie | 2 | Distribution stats |
| erDiagram | 1 | Data models |

## Interleaving Protocol

### 1. Random Selection (Entropy-Seeded)

```bash
# Get random diagram by trit
duckdb ~/mermaid_diagrams.duckdb "
  SELECT content FROM diagrams 
  WHERE trit = (SELECT (random() * 3 - 1)::int % 3)
  ORDER BY random() LIMIT 1
"
```

### 2. Type-Matched Selection

```bash
# Match diagram type to context
duckdb ~/mermaid_diagrams.duckdb "
  SELECT content FROM diagrams 
  WHERE diagram_type = 'flowchart'
  ORDER BY random() LIMIT 1
"
```

### 3. GF(3) Balanced Triad

```bash
# Get one diagram per trit for balanced presentation
duckdb ~/mermaid_diagrams.duckdb "
  (SELECT content, trit FROM diagrams WHERE trit = -1 ORDER BY random() LIMIT 1)
  UNION ALL
  (SELECT content, trit FROM diagrams WHERE trit = 0 ORDER BY random() LIMIT 1)
  UNION ALL
  (SELECT content, trit FROM diagrams WHERE trit = 1 ORDER BY random() LIMIT 1)
"
```

## Usage Triggers

Interleave a bmorphism diagram when:

1. **Architecture discussions** → flowchart/graph
2. **Protocol design** → sequenceDiagram/stateDiagram  
3. **Data modeling** → erDiagram/classDiagram
4. **Skill loading** → graph (skill dependencies)
5. **Random inspiration** → any type, entropy-seeded

## Rendering

Use the `mermaid` tool to render selected diagrams:

```
mermaid(code=DIAGRAM_CONTENT, citations={})
```

## Example Workflow

```bash
# 1. Query a contextual diagram
DIAGRAM=$(duckdb ~/mermaid_diagrams.duckdb -noheader -list "
  SELECT content FROM diagrams 
  WHERE diagram_type = 'flowchart' 
  AND content LIKE '%GF(3)%'
  ORDER BY random() LIMIT 1
")

# 2. Render via mermaid tool
# mermaid(code=$DIAGRAM, citations={})
```

## Trit Assignment

Diagrams inherit trits from content analysis:

- **MINUS (-1)**: Validation, constraints, error states
- **ERGODIC (0)**: Neutral flows, queries, observations  
- **PLUS (+1)**: Generation, creation, composition

## Stats Query

```bash
duckdb ~/mermaid_diagrams.duckdb "
  SELECT 
    diagram_type,
    COUNT(*) as count,
    SUM(CASE WHEN trit = -1 THEN 1 ELSE 0 END) as minus,
    SUM(CASE WHEN trit = 0 THEN 1 ELSE 0 END) as ergodic,
    SUM(CASE WHEN trit = 1 THEN 1 ELSE 0 END) as plus
  FROM diagrams 
  GROUP BY diagram_type 
  ORDER BY count DESC
"
```
