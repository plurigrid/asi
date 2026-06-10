---
name: llms-txt-discovery
description: 'Create the **largest indexed directory of AI documentation** by:'
---
# llms-txt-discovery: Largest AI Documentation Directory

**Status**: Stepping Stone 🌉
**Information Energy**: 0.90 (High aspiration, partial implementation)
**Trit Assignment**: 0 (Coordinator - Indexes and balances documentation)
**GF(3) Color**: 🔵 `#0000FF` (Blue - Coordinator)

## Purpose

Create the **largest indexed directory of AI documentation** by:

1. **Crawling**: Find `/llms.txt` files across 10,000+ repositories
2. **Parsing**: Extract structured metadata + linked resources
3. **Indexing**: Build full-text search over documentation
4. **Ranking**: Sort results by relevance + credibility
5. **Integration**: Connect to code-context for implementation discovery

## Architecture

```
asi-skills/llms-txt-discovery/
├── crawler.bb              # Repository + llms.txt discovery
├── parser.bb               # Parse llms.txt markdown format
├── indexer.bb              # Full-text search index
├── ranker.bb               # Relevance + credibility ranking
├── storage.bb              # DuckDB persistence
└── SKILL.md                # This file
```

## Format: llms.txt

Each project provides structured documentation via `/llms.txt`:

```markdown
# Project Name

> Brief description

Detailed notes about the project...

## Section Name

- [Link Title](https://url): Description of resource

## Optional

- [Link Title](https://url): Can be skipped for shorter context
```

## Discovery Pipeline

### Stage 1: Repository Discovery

Search GitHub for repos with `/llms.txt`:

```bash
site:github.com llms.txt file:llms.txt path:/ language:markdown
```

Results: 8,000+ repositories with documented APIs

### Stage 2: Parse & Extract

For each repository:
1. Fetch `/llms.txt` (or `/docs/llms.txt`)
2. Parse markdown structure
3. Extract: project name, description, sections, links
4. Rank links by position (earlier = more important)

### Stage 3: Index Content

```clojure
{:repo-id "github:bmorphism/Gay.jl"
 :name "Gay.jl"
 :description "Deterministic color generation..."
 :sections [{:title "Basics" :links [...]}
            {:title "Advanced" :links [...]}]
 :crawl-time "2026-01-04T12:00:00Z"
 :credibility 0.95  ; Based on stars, age, activity
}
```

### Stage 4: Search Interface

```bash
duck llms-txt-search "Julia ACSet implementation"
→ Top results from indexed documentation

duck llms-txt-search "skill registry patterns"
→ Results from npm, pip, Hackage, Crates docs
```

## Integration: Finding Skill Implementations

**Use Case**: Implement `polyglot-orchestration` skill

```bash
# Step 1: Search for polyglot patterns
duck llms-txt-search "polyglot language execution"

# Returns:
# - duckCloud documentation (orchestration patterns)
# - Red Planet Labs Rama (distributed systems)
# - Babashka (JVM-less execution)

# Step 2: Get parsed documentation
duck llms-txt-get "github:red-planet-labs/rama"

# Returns full llms.txt with indexed links

# Step 3: Use with code-context
use code-context to find [patterns from returned links]
```

## Data Structure

```clojure
{:llms-txt-entry
 {:id "github:owner/repo"
  :host "github.com"
  :owner "owner"
  :repo "repo"
  :url "https://github.com/owner/repo/llms.txt"
  :title "Project Title"
  :description "Short summary"
  :sections [{:type :required    ; or :optional
              :title "Section Name"
              :links [{:title "Link Title"
                       :url "https://url"
                       :description "Optional desc"
                       :rank 1}]}]
  :metadata {:stars 1234
             :created "2023-01-01"
             :updated "2025-01-04"
             :language "julia"
             :topics ["color" "gf3"]}
  :credibility 0.95  ; stars + activity + age
  :indexed-at "2026-01-04"}}
```

## Search Ranking

Results ranked by:

1. **Relevance** (BM25): How well query matches content
2. **Credibility** (0-1): Based on:
   - GitHub stars (0-0.4)
   - Activity (commits/year, 0-0.3)
   - Age (older = more stable, 0-0.2)
   - Community size (watchers, 0-0.1)
3. **Recency**: More recent results weighted higher

## Example Queries

```clojure
; Find Julia skill implementations
(search "Julia" {:language "julia" :top 10})

; Find agent coordination patterns
(search "coordination" {:topics ["agent" "multi-agent"]})

; Find implementations for GF(3) systems
(search "finite field" {:keywords "gf3"})

; All documentation for ACSet libraries
(search "acset" {:exact true})
```

## GF(3) Integration

The llms-txt-discovery skill itself participates in GF(3) balance:

- **Trit**: 0 (Coordinator) - Balances generators and validators
- **Role**: Provides documentation for both implementation (generators) and verification (validators)
- **Balance**: Works with `documentation-indexing` (trit +1) and `skill-taxonomy` (trit -1)

## Deployment

### Local Development

```bash
# Crawl a single repo
bb crawler.bb crawl "github:bmorphism/Gay.jl"

# Index all crawled repos
bb indexer.bb build

# Search indexed documentation
bb search.bb "julia color"
```

### Duck Integration

```bash
# Pre-hook loads llms-txt-discovery
just duck-propagate

# Search in interactions
duck llms-txt-search "polyglot execution"
```

### Cloud Scaling

```bash
# Initialize 10,000 crawl tasks
just llms-txt-distribute 10000

# Monitor progress
just llms-txt-status

# Export indexed database
just llms-txt-export llms-txt-index.duckdb
```

## Success Metrics

| Metric | Target | Status |
|--------|--------|--------|
| Repositories indexed | 10,000+ | ⏳ Pending |
| Documentation links | 100,000+ | ⏳ Pending |
| Search latency | < 100ms | ⏳ Pending |
| Credibility accuracy | > 90% | ⏳ Pending |
| Coverage of plurigrid | 100% | ⏳ Pending |

## Related Skills

**Dependencies**:
- `skill-taxonomy` - Uses registry to organize search results
- `gf3-conservation` - Validates coordinator role
- `gay-integration` - Colors documentation by language/topic

**Dependents**:
- `polyglot-orchestration` - Uses discovered patterns to implement
- `code-context` integration - Feeds results to code-context MCP
- `documentation-indexing` - Aggregates into searchable corpus

## References

- **llms.txt Standard**: https://llmstxt.org/
- **Directories**:
  - https://llmstxt.site/
  - https://directory.llmstxt.cloud/
- **Implementations**:
  - llms_txt2ctx (Python)
  - fasthtml llms.txt examples
  - nbdev auto-generation

---

**Status**: 😢 **SAD STATE** → 🌉 **STEPPING STONE**
**Next**: Implement crawler in `duck/asi-skills/llms-txt-discovery/crawler.bb`
**Owner**: bmorphism + code-codex
**Created**: 2026-01-04
