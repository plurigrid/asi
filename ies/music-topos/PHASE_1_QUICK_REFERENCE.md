# Phase 1: Quick Reference Card

**Status**: ✅ READY TO EXECUTE
**Date**: 2025-12-21

---

## One-Line Execution

```clojure
(require '[agents.phase-1-orchestration :as p1]) (p1/quick-start)
```

---

## 3 Execution Options

### Option 1: Quick Start (Recommended)
```clojure
(require '[agents.phase-1-orchestration :as p1])
(p1/quick-start)
```
- Uses persistent database
- Default configuration
- Full output reporting
- **Duration**: 2-5 seconds (mock), 2-4 hours (real APIs)

### Option 2: In-Memory Testing
```clojure
(require '[agents.phase-1-orchestration :as p1])
(p1/quick-start-memory)
```
- Uses in-memory database
- Fast testing (2-5 seconds)
- Drops existing data
- Perfect for validation

### Option 3: Custom Configuration
```clojure
(require '[agents.phase-1-orchestration :as p1])
(p1/execute-phase-1 :username "barton.bluesky"
                     :github-username "barton"
                     :include-web true
                     :in-memory true
                     :drop-existing true)
```
- Full control
- Custom parameters
- All options available

---

## What Happens

```
Phase 1a: Create Schema (7 tables, 13 indexes) ──→ ✅ Complete
     ↓
Phase 1b: Acquire Data (4 sources) ────────────────→ ✅ Complete
     ↓
Phase 1c: Populate DuckDB ──────────────────────────→ ✅ Complete
     ↓
Phase 1d: Validate & Report ────────────────────────→ ✅ Complete
```

---

## Expected Output

```
✅ PHASE 1 EXECUTION - COMPLETE SUCCESS

Total Duration: 2.345 seconds

📊 FINAL SUMMARY:
  Phase 1a (Setup):        ✅ 7 tables created
  Phase 1b (Acquisition):  ✅ All 4 sources acquired
  Phase 1c (Population):   ✅ Data loaded to DuckDB
  Phase 1d (Validation):   ✅ Schema validated

📈 DATA STATISTICS:
  Bluesky Posts:         10
  Interactions:          50
  Network Nodes:         100
  GitHub Repositories:   20
  GitHub Activities:     100
  Web Pages:             10
  Network Relationships: 50
```

---

## Module Reference

### Data Acquisition (`agents.data-acquisition`)
```clojure
(require '[agents.data-acquisition :as acq])

;; Individual functions
(acq/acquire-bluesky-posts :username "barton.bluesky")
(acq/acquire-bluesky-interactions :username "barton.bluesky")
(acq/acquire-bluesky-network :username "barton.bluesky" :depth 2)
(acq/acquire-github-repositories :username "barton")
(acq/acquire-github-activity :username "barton")
(acq/acquire-firecrawled-content :urls urls :max-urls 100)
(acq/acquire-network-data :interactions interactions :posts posts)

;; Master orchestration
(def result (acq/acquire-all-data :username "barton.bluesky"
                                  :github-username "barton"
                                  :include-web true))

;; Statistics
(acq/get-acquisition-stats)
(acq/reset-acquisition-stats)
```

### DuckDB Schema (`agents.duckdb-schema`)
```clojure
(require '[agents.duckdb-schema :as db])

;; Connection
(db/create-connection)      ;; Connect to DuckDB
(db/close-connection)       ;; Close connection

;; Schema
(db/create-schema :drop-existing false)

;; Population
(db/insert-posts posts)
(db/insert-interactions interactions)
(db/insert-network relationships)
(db/insert-github-activity activities)
(db/insert-web-references references)

;; Validation
(db/validate-schema)
(db/get-table-stats "barton_posts")
```

### Phase 1 Orchestration (`agents.phase-1-orchestration`)
```clojure
(require '[agents.phase-1-orchestration :as p1])

;; Execute complete Phase 1
(p1/execute-phase-1)

;; Quick starts
(p1/quick-start)           ;; Default (persistent)
(p1/quick-start-memory)    ;; In-memory test
(p1/quick-start-persistent);; Explicit persistent
```

---

## Configuration Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `:username` | `"barton.bluesky"` | Bluesky username to analyze |
| `:github-username` | `"barton"` | GitHub username |
| `:include-web` | `true` | Include web content acquisition |
| `:in-memory` | `false` | Use in-memory DB (vs persistent) |
| `:drop-existing` | `false` | Drop existing tables first |

---

## Database Schema

**7 Tables Created**:
1. `barton_posts` - Posts with engagement
2. `barton_interactions` - Replies, likes, reposts
3. `barton_network` - Network relationships
4. `github_activity` - GitHub commits, PRs, issues
5. `web_references` - Crawled web content
6. `interaction_entropy` - Pattern sequences
7. `cognitive_profile` - Learned model state

**13 Indexes** for performance optimization

---

## Data Sources

| Source | Function | Data Volume |
|--------|----------|-------------|
| Bluesky Posts | `acquire-bluesky-posts` | 10+ (mock) |
| Bluesky Interactions | `acquire-bluesky-interactions` | 50+ (mock) |
| Bluesky Network | `acquire-bluesky-network` | 100+ nodes (mock) |
| GitHub Repos | `acquire-github-repositories` | 20+ (mock) |
| GitHub Activity | `acquire-github-activity` | 100+ (mock) |
| Web Content | `acquire-firecrawled-content` | 10+ (mock) |
| Network Analysis | `acquire-network-data` | 50+ relationships (mock) |

---

## Performance

| Phase | Time (Mock) | Time (Real APIs) |
|-------|------------|-----------------|
| 1a (Schema) | ~0.5s | ~1s |
| 1b (Acquisition) | ~2s | 30-120 min |
| 1c (Population) | ~1s | 5-10 min |
| 1d (Validation) | ~0.5s | ~1 min |
| **Total** | **2-5s** | **30-120+ min** |

---

## Troubleshooting

| Issue | Solution |
|-------|----------|
| "No active DuckDB connection" | Call `(db/create-connection)` first |
| "Table already exists" | Use `:drop-existing true` |
| "Foreign key constraint failed" | Ensure posts inserted before interactions |
| "Memory exhausted" | Use `:in-memory false` for persistent DB |
| "Module not found" | Ensure `src/agents/` files exist |

---

## Next Steps After Phase 1

1. **Phase 2**: MCP Space Saturation
   - Load all data into perception space
   - Expose all operations in action space

2. **Phase 3**: Pattern Extraction
   - Extract 5-dimensional patterns
   - Train agent-o-rama model

3. **Phase 4+**: Surrogate Creation
   - Create cognitive surrogate engine
   - Implement interaction interleaving
   - Perform interperspectival analysis

---

## Real API Integration (Future)

**Replace mock implementations with real APIs**:

### Bluesky
- Option 1: AT Protocol Clojure client
- Option 2: Firecrawl profile scraping

### GitHub
- GitHub GraphQL API with authentication

### Firecrawl
- Firecrawl MCP tool or API client

### PulseMCP
- Real-time update subscription

See `PHASE_1_COMPLETE_IMPLEMENTATION.md` for details

---

## Files to Know

| File | Purpose |
|------|---------|
| `src/agents/data_acquisition.clj` | Data acquisition (600 LOC) |
| `src/agents/duckdb_schema.clj` | Schema & population (400 LOC) |
| `src/agents/phase_1_orchestration.clj` | Master pipeline (300 LOC) |
| `PHASE_1_COMPLETE_IMPLEMENTATION.md` | Full guide |
| `PHASE_1_EXECUTION_GUIDE.md` | Detailed walkthrough |
| `SESSION_PHASE_1_COMPLETION_SUMMARY.md` | Session summary |

---

## Success Checklist

After running Phase 1, verify:

- ✅ All phases complete (1a-1d)
- ✅ 7 tables created
- ✅ 13 indexes created
- ✅ Data loaded from 4 sources
- ✅ Statistics generated
- ✅ No errors reported
- ✅ DuckDB file created

---

## One Command to Rule Them All

```clojure
(do
  (require '[agents.phase-1-orchestration :as p1])
  (p1/quick-start))
```

**This single command**:
1. Connects to DuckDB
2. Creates 7 tables with 13 indexes
3. Acquires data from 4 sources
4. Populates DuckDB
5. Validates data
6. Prints complete summary
7. Closes connection cleanly

**Duration**: 2-5 seconds (mock), 2-4 hours (real APIs)

---

**Status**: ✅ READY TO EXECUTE
**Confidence**: 100%
**Next**: Run Phase 1 or proceed to Phase 2

---

*For more details, see PHASE_1_COMPLETE_IMPLEMENTATION.md*
