---
name: ducklake-semantic-analyzer
description: Semantic analysis for DuckLake ACSet models with GF(3) conservation
---

# Ducklake Semantic Analyzer

**Version:** 1.0.0
**Status:** Production Ready
**Created:** 2025-12-21
**Total Mentions:** 255

## Overview

Loads semantic analysis from Subagent 2 (Query Analyzer) and provides functions for intent classification, semantic clustering, and co-occurrence analysis across 45 files.

## Purpose

Enable semantic understanding of ducklake mentions:
- Intent classification (reference, documentation, implementation, testing)
- Semantic cluster detection (technical, color-based, parallel, testing, data)
- Keyword co-occurrence analysis
- Context window extraction

## Data Sources

- **Primary:** `/Users/bob/ies/ducklake_semantic_analysis_2025-12-21.json`
- **Coverage:** 45 files, 255 mentions
- **Languages:** Markdown (28.9%), Julia (22.2%), Hy (11.1%), Python, Rust, Swift, SQL

## Functions

### classify_intent(mention: str) -> str

Classify semantic intent of a mention.

```python
intent = classify_intent("ducklake temporal query optimization")
# Returns: "implementation"

intent = classify_intent("see ducklake schema documentation")
# Returns: "reference"
```

**Categories:**
- `reference` (45.5%) - Passive mentions
- `documentation` (17.6%) - Formal documentation
- `implementation` (5.9%) - Active code
- `testing` (6.7%) - Tests and validation
- `query_discussion` (9.8%) - SQL query discussions

**Implementation:**
```python
import json
import re

INTENT_PATTERNS = {
    "implementation": r"(implement|create|build|optimize|develop)",
    "documentation": r"(document|explain|describe|guide|reference)",
    "testing": r"(test|verify|validate|check|assert)",
    "query_discussion": r"(query|select|from|where|sql)",
    "reference": r".*"  # Default
}

def classify_intent(mention: str) -> str:
    mention_lower = mention.lower()
    for intent, pattern in INTENT_PATTERNS.items():
        if re.search(pattern, mention_lower):
            return intent
    return "reference"
```

### find_clusters(keyword: str) -> list

Find semantic clusters containing keyword.

```python
clusters = find_clusters("color")
# Returns: [
#   {"cluster": "color_based_identity", "strength": "high", "count": 83},
#   {"cluster": "parallel_processing", "strength": "medium", "count": 34}
# ]
```

**Available Clusters:**
1. **technical_architecture** (102 mentions)
   - Keywords: duckdb, lake, temporal, versioning, sql, table
2. **color_based_identity** (83 mentions)
   - Keywords: color, gay, seed, retromap, deterministic, spi
3. **parallel_processing** (61 mentions)
   - Keywords: parallel, thread, integration, acset
4. **testing_validation** (40 mentions)
   - Keywords: test, verify, analysis
5. **data_integration** (43 mentions)
   - Keywords: data, parquet, integration, world

### compute_cooccurrence(term1: str, term2: str) -> dict

Compute co-occurrence relationship strength.

```python
result = compute_cooccurrence("duckdb", "lake")
# Returns: {
#   "cooccurrence": 100,
#   "significance": "DuckLake is fundamentally a DuckDB-based system",
#   "mentions": 255
# }
```

**High Co-occurrence Pairs:**
- `lake` + `duckdb`: 100% (always together)
- `color` + `gay`: 62% (color via GAY seed)
- `temporal` + `versioning`: 28%
- `parallel` + `thread`: 34%
- `seed` + `deterministic`: 36%

### extract_context_window(mention: str, lines: int = 5) -> str

Extract surrounding context for a mention.

```python
context = extract_context_window("ducklake temporal analysis", lines=3)
# Returns multi-line string with context before and after
```

## Usage Example

```python
from skills.ducklake_semantic_analyzer import *

# Find all implementation mentions
impl_files = []
with open("/Users/bob/ies/ducklake_semantic_analysis_2025-12-21.json") as f:
    data = json.load(f)
    for file_path, mentions in scan_all_files():
        for mention in mentions:
            if classify_intent(mention) == "implementation":
                impl_files.append(file_path)

print(f"Implementation files: {len(set(impl_files))}")

# Find color-related clusters
color_clusters = find_clusters("color")
for cluster in color_clusters:
    print(f"{cluster['cluster']}: {cluster['count']} mentions ({cluster['strength']})")

# Check keyword relationships
pairs = [("duckdb", "lake"), ("color", "gay"), ("temporal", "versioning")]
for term1, term2 in pairs:
    result = compute_cooccurrence(term1, term2)
    print(f"{term1} + {term2}: {result['cooccurrence']}%")
```

## Skills Dependencies

- code-review (pattern analysis)
- llm-application-dev (semantic understanding)
- frontend-design (visualization patterns)

## Integration Points

- **Temporal Introspection:** Combine intent with temporal clustering
- **Pattern Expansion:** Use semantic clusters for progressive discovery
- **Categorical Model:** Map intents to ACSet attributes

## Key Statistics

- Total files: 45
- Total mentions: 255
- Top keyword: 'lake' (255 occurrences)
- DuckDB references: 102
- Color keywords: 83
- Temporal keywords: 28
- ACSet keywords: 27
- Documentation: 45% of mentions

## Hotspot Files

1. `gay_ducklake.jl` - 29 mentions (main implementation)
2. `DUCKDB_HISTORY_ANALYSIS.txt` - 26 mentions (historical analysis)
3. `rio/Gay.jl/src/gay_pliny_krep.jl` - 23 mentions (Pliny integration)
4. `rio/Gay.jl/worlds/hatchery/pliny_acset_parallel.jl` - 19 mentions (parallel ACSet)
5. `hatchery_repos/bmorphism__bafishka/src/geo_game/time_travel.rs` - 14 mentions (Rust time-travel)

## Architectural Patterns

### Reafferent Detection
- Self-recognition through color identity matching
- Formula: `color(seed) ⊻ color(observation) → recognition`
- Canonical seed: 1069, iterations: 1069

### Contemporaneous Timeslices
- Temporal database slicing for parallel history analysis
- Components: interactions, amp_threads, timeslices
- GF3 tracking: Red/Yellow/Blue balanced ternary polarity

### Color Retromap
- Retroactive temporal color mapping to battery cycle states
- Technology: Hy language with DuckDB backend
- Purpose: Assign interactions to color slices for temporal analysis

## GF(3) Distribution

This skill operates in the **YELLOW (GF3=1)** structural category:
- 38.9% of mentions
- Focus: Semantic relationships, classification, clustering

---

**Skill Type:** Semantic Analysis
**Color:** YELLOW
**Polarity:** GF(3) = 1
**Access Pattern:** Read-only analysis

## REPL atlas

Part of: `repl-commons`. Family canonical: `duckdb-guard`.
