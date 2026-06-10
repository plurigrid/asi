---
name: documentation-indexing
description: 'Provide **full-text search, semantic indexing, and relevance ranking** across all documentation:'
---
# documentation-indexing: Unified Full-Text Search + Ranking

**Status**: SAD STATE → IMPLEMENTATION 🌟
**Information Energy**: 0.87 (High aspiration, maximum sadness)
**Trit Assignment**: 0 (COORDINATOR - Balances generators and validators)
**GF(3) Color**: #49EE54 (Green - Equilibrium point)

## Purpose

Provide **full-text search, semantic indexing, and relevance ranking** across all documentation:
- Skill registry (69 skills)
- Language docs (llms.txt standard)
- Blog posts / tutorials
- Source code docstrings
- DuckDB database schemas

**Key capabilities:**
1. **Full-Text Search**: Keyword + fuzzy matching (BM25 algorithm)
2. **Semantic Ranking**: TF-IDF + recency + community signals
3. **Multi-Source Indexing**: Consolidate docs from heterogeneous sources
4. **Metadata Extraction**: Automatically parse headers, links, code blocks
5. **Bi-Directional Navigation**: Move between docs ↔ implementations

## Architecture

```
┌──────────────────────────────────────────────────────────────────┐
│              DOCUMENTATION INDEXING (GREEN COORDINATOR)          │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┬──────────────┬──────────────┐                 │
│  │   llms.txt   │   README.md  │  Code Docs   │                 │
│  │  Discovery   │   Crawlers   │  Extractors  │                 │
│  └──────┬───────┴──────┬───────┴──────┬───────┘                 │
│         │               │               │                       │
│         ▼──────────────▼───────────────▼                        │
│  ┌────────────────────────────────────────┐                    │
│  │    Metadata Normalization Layer        │                    │
│  │  • Title extraction (H1 → h1)          │                    │
│  │  • Link parsing (Markdown → URL)       │                    │
│  │  • Code fence detection ([```] → ...)  │                    │
│  │  • Authority scoring (stars, forks)    │                    │
│  └────────────┬──────────────────────────┘                     │
│               │                                                 │
│               ▼                                                 │
│  ┌────────────────────────────────────────┐                    │
│  │      Inverted Index (DuckDB)           │                    │
│  │  ┌──────────────────────────────────┐  │                    │
│  │  │ term_id | term | doc_id | rank  │  │                    │
│  │  │ 1       | gay  | 42     | 0.89  │  │                    │
│  │  │ 2       | mcp  | 42     | 0.76  │  │                    │
│  │  │ 3       | api  | 71     | 0.65  │  │                    │
│  │  └──────────────────────────────────┘  │                    │
│  └────────────┬───────────────────────────┘                    │
│               │                                                 │
│               ▼                                                 │
│  ┌────────────────────────────────────────┐                    │
│  │    BM25 Ranker + Result Aggregator     │                    │
│  │  • Cross-language result merging       │                    │
│  │  • Deduplication (canonical URLs)      │                    │
│  │  • Community signals (upvotes, stars)  │                    │
│  └────────────┬───────────────────────────┘                    │
│               │                                                 │
│               ▼                                                 │
│  ┌────────────────────────────────────────┐                    │
│  │   Result Cache (< 1 second latency)    │                    │
│  │   [query → ranked results + metadata]  │                    │
│  └────────────────────────────────────────┘                    │
│                                                                  │
│  GF(3) BALANCE: (-1 extractor) ⊗ (0 indexer) ⊗ (+1 ranker)     │
└──────────────────────────────────────────────────────────────────┘
```

## Data Model

### Documents Index

```sql
CREATE TABLE documentation_index (
  doc_id INT PRIMARY KEY,
  source VARCHAR,                 -- 'github', 'llms-txt', 'blog'
  repo_id VARCHAR,               -- 'bmorphism/Gay.jl'
  title VARCHAR,
  url VARCHAR,
  body TEXT,                      -- Full document text
  headers TEXT[],                 -- H1, H2, H3 hierarchy
  links TEXT[],                   -- Embedded links
  code_blocks TEXT[],             -- [```lang ... ```]
  stars INT,                      -- GitHub stars
  forks INT,                       -- GitHub forks
  updated_at TIMESTAMP,
  indexed_at TIMESTAMP,
  trit TINYINT                    -- GF(3) assigned (0)
);
```

### Terms Inverted Index

```sql
CREATE TABLE term_index (
  term_id INT PRIMARY KEY,
  term VARCHAR,
  term_lower VARCHAR,
  frequency INT,                  -- TF (term frequency)
  doc_count INT,                  -- DF (document frequency)
  bm25_idf FLOAT,                 -- Precomputed IDF
  created_at TIMESTAMP
);

CREATE TABLE term_doc_map (
  term_id INT,
  doc_id INT,
  frequency INT,                  -- TF in this doc
  position INT[],                 -- Token positions
  context VARCHAR,                -- Surrounding text
  relevance_score FLOAT,          -- BM25(tf, idf, doc_len)
  PRIMARY KEY (term_id, doc_id)
);
```

## API / Interfaces

### Simple Text Search

```clojure
;; Search docs
(search-docs {:query "gay"
              :type :keyword
              :limit 10
              :min-score 0.3})
→ [{:title "Gay.jl"
    :url "https://github.com/bmorphism/Gay.jl"
    :score 0.95
    :snippet "Gay.jl: Deterministic color generation..."}
   ...]

;; Fuzzy search (typo tolerance)
(search-docs {:query "gey"              ; typo
              :fuzzy true
              :distance 1})
→ (Results for "gay" with edit distance ≤ 1)

;; Advanced: Boolean search
(search-docs {:query "(gay OR color) AND julia"
              :type :boolean})
```

### Metadata Search

```clojure
;; Find docs by category
(search-by-metadata {:source "github"
                     :stars {:min 100 :max 1000}})
→ [Gay.jl, ACSets.jl, Duck, ...]

;; Find recent updates
(search-by-metadata {:updated-after "2025-12-01"
                     :source "blog"})
→ [Latest blog posts, ...]

;; Filter by language
(search-by-metadata {:languages ["Julia" "Clojure" "Babashka"]})
```

### Bidirectional Navigation

```clojure
;; Find implementations of a doc
(doc-implementations {:doc-id 42})
→ [{:file "src/gay.jl"
    :lines [1 42]
    :snippet "function seed!(rng)..."}]

;; Find docs for implementation
(implementation-docs {:file "src/gay.jl"
                      :line 10})
→ [{:doc-id 42
    :title "Gay.jl API Reference"
    :section "seed! function"}]

;; Find related docs
(related-docs {:doc-id 42
               :semantic true})
→ [ACSets.jl, GF(3) docs, ...]
```

## GF(3) Trit Assignment

```
documentation-indexing → 0 (COORDINATOR)
  Balances extraction (-1) ↔ ranking/generation (+1)
  Maintains middle ground for all doc types

Triadic system:
  source-extractor (-1 validator)   → pulls raw docs
  indexing (0 coordinator)          → organizes & indexes
  result-ranker (+1 generator)      → produces ranked results

  Sum: (-1) + (0) + (+1) = 0 ✓ GF(3) CONSERVED
```

## Implementation Strategy

### Stage 1: Term Extraction (Days 1-2)

Create `/Users/bob/iii/duck/asi-skills/documentation-indexing/extractor.bb`:
- Markdown parser → extract H1-H4, links, code blocks
- Tokenizer → split text into terms
- Stopword filter → remove common words
- Store in DuckDB `term_index`

### Stage 2: Inverted Index Builder (Days 3-4)

Create `indexer.bb`:
- BM25 IDF calculation
- TF per document
- Relevance scoring
- Populate `term_doc_map`

### Stage 3: Search Engine (Days 5-6)

Create `searcher.bb`:
- Boolean query parser
- Fuzzy matching (Levenshtein)
- Result ranking by score
- Caching layer

### Stage 4: Multi-Source Integration (Days 7-8)

- Crawl llms.txt repositories
- Index GitHub README files
- Extract docstrings from source
- Verify GF(3) balance across sources

## Example: Semantic Search Pipeline

```clojure
;; User query
(search-docs {:query "how to generate deterministic colors in julia"})

Step 1: Extract terms (-1 validator)
  ["deterministic" "colors" "julia"]

Step 2: Index lookup (0 coordinator)
  Fetch docs matching all terms
  Calculate BM25 score per doc

Step 3: Rank and aggregate (+1 generator)
  1. Gay.jl (0.95)
  2. GF(3) Integration (0.72)
  3. Color Theory (0.68)

Result: Σ(-1, 0, +1) = 0 ✓
```

## Success Metrics

| Metric | Target | Status |
|--------|--------|--------|
| Docs indexed | 500+ (skills + readmes + blogs) | ⏳ Pending |
| Search latency | <100ms p95 | ⏳ Pending |
| Precision (top-5) | ≥0.8 | ⏳ Pending |
| Recall | ≥0.75 | ⏳ Pending |
| Fuzzy tolerance | Edit distance ≤ 2 | ⏳ Pending |
| GF(3) balance | All pipeline stages ≡ 0 (mod 3) | ⏳ Pending |

## Related Skills

**Dependencies:**
- `skill-taxonomy` - Registry of docs to index
- `acsets` - Schema for index structure
- `llms-txt-discovery` - Crawl source docs

**Dependents:**
- `polyglot-orchestration` - Search polyglot docs
- `skill-dispatch` - Route searches to relevant skills
- `world-knowledge-base` - Unified doc interface

## References

- BM25 algorithm: https://en.wikipedia.org/wiki/Okapi_BM25
- Inverted index: Classic IR data structure
- Levenshtein distance: Fuzzy string matching
- TF-IDF: Term weighting scheme
- DuckDB FTS: Full-text search extension

---

**Status**: 😢 **SAD STATE** → 🌟 **IMPLEMENTING**
**Color**: #49EE54 (Green Coordinator)
**Next**: Create `extractor.bb` (term extraction)
**Owner**: GREEN AGENT (0)
**Created**: 2026-01-04
