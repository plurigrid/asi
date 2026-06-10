---
name: data-science-cli
description: Unix command-line tools for data science workflows. Filesystem changes tracked by color for retrieval.
---
# Data Science on the Command Line

**Color**: #2518AA (deep indigo)  
**Trit**: -1 (MINUS - validation/analysis)  
**URI**: `skill://data-science-cli#2518AA`

---

## Overview

Unix command-line tools for data science workflows. Filesystem changes tracked by color for retrieval.

## Filesystem Change Operations by Color

| Operation | Trit | Color | Commands |
|-----------|------|-------|----------|
| **CREATE** | +1 | 🔴 warm | `touch`, `mkdir`, `>`, `tee` |
| **TRANSFORM** | 0 | 🟢 neutral | `sed`, `awk`, `cut`, `sort`, `uniq` |
| **DELETE/FILTER** | -1 | 🔵 cold | `rm`, `grep -v`, `head`, `tail` |

## Core Tools

### Data Acquisition (+1 Generator)
```bash
curl -sL URL | jq .                    # Fetch JSON
wget -qO- URL                          # Stream download
cat file.csv                           # Read local
```

### Data Transformation (0 Coordinator)
```bash
# CSV processing
csvkit: csvcut, csvgrep, csvsort, csvjoin
miller (mlr): mlr --csv filter/cut/sort

# JSON processing  
jq '.[] | select(.field > 10)'
gron file.json | grep pattern | gron -u

# Text streams
awk -F',' '{print $1, $3}'
sed 's/old/new/g'
cut -d',' -f1,3
sort -t',' -k2 -n
uniq -c
```

### Data Validation (-1 Validator)
```bash
wc -l file.csv                         # Row count
head -1 file.csv | tr ',' '\n' | nl    # Schema
csvstat file.csv                       # Statistics
datamash -t',' mean 2 < file.csv       # Aggregates
```

## Pipeline Patterns

### ETL Pipeline (GF(3) = 0)
```bash
# +1: Extract
curl -s api.example.com/data |
# 0: Transform  
jq '.items[]' |
# -1: Load/Validate
tee output.json | wc -l
```

### Filesystem Watch + Log
```bash
# Track changes with fswatch + color tagging
fswatch -0 /path | while read -d '' event; do
  trit=$(echo "$event" | shasum | cut -c1)
  case $trit in
    [0-5]) color="warm";;   # +1
    [6-a]) color="neutral";; # 0
    [b-f]) color="cold";;    # -1
  esac
  echo "[$color] $event" >> fs_changes.log
done
```

### DuckDB Integration
```bash
# Query CSV directly
duckdb -c "SELECT * FROM 'data.csv' WHERE col > 10"

# Parquet conversion
duckdb -c "COPY (SELECT * FROM 'data.csv') TO 'data.parquet'"

# Time-travel queries (with temporal versioning)
duckdb fs_changes.duckdb <<SQL
  SELECT * FROM changes 
  WHERE timestamp > now() - INTERVAL '1 hour'
  ORDER BY timestamp DESC
SQL
```

## Color-Indexed Retrieval

```bash
# Find all +1 (create) operations
grep '\[warm\]' fs_changes.log

# Find all -1 (delete/filter) operations  
grep '\[cold\]' fs_changes.log

# GF(3) conservation check
awk '/warm/{w++}/neutral/{n++}/cold/{c++} END{print (w-c)%3}' fs_changes.log
```

## Key Commands Reference

| Tool | Purpose | Trit |
|------|---------|------|
| `jq` | JSON processor | 0 |
| `mlr` | CSV/JSON swiss army knife | 0 |
| `csvkit` | CSV utilities | 0 |
| `datamash` | Statistics | -1 |
| `pv` | Progress monitoring | 0 |
| `parallel` | Parallel execution | +1 |
| `xargs` | Argument distribution | 0 |
| `tee` | Stream splitting | +1 |
| `comm` | Set operations | -1 |
| `join` | Relational join | 0 |

## Triad Bundle

```
duck-agent (-1) ⊗ data-science-cli (-1) ⊗ ??? (+2)
```

Needs +2 to balance — combine with two +1 skills or one +1 generator.

---

**Skill Name**: data-science-cli  
**Type**: Command-Line Data Science  
**Trit**: -1 (MINUS)  
**GF(3)**: Requires balancing with generator skills

Base directory: file:///Users/bob/iii/.agents/skills/data-science-cli
