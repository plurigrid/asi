# Phase 1: Data Acquisition - Complete Implementation Plan

**Date**: 2025-12-21
**Status**: Starting Phase 1
**Objective**: Acquire all @barton data from 4 sources and populate DuckDB
**Timeline**: Depends on data availability

---

## Overview

Phase 1 is the data foundation layer that feeds all subsequent phases. We need to acquire @barton's complete digital footprint across 4 major sources:

```
┌─────────────────────────────────────────────┐
│ PHASE 1: DATA ACQUISITION                   │
├─────────────────────────────────────────────┤
│                                             │
│ 1. Bluesky API                              │
│    └─ All @barton.bluesky posts             │
│    └─ All interactions (replies, likes)     │
│    └─ Engagement metrics                    │
│                                             │
│ 2. GitHub GraphQL API                       │
│    └─ All @barton repositories              │
│    └─ Commits, PRs, issues                  │
│    └─ Collaboration network                 │
│                                             │
│ 3. Firecrawl (Web Content)                  │
│    └─ URLs referenced in posts              │
│    └─ Full page content                     │
│    └─ Metadata extraction                   │
│                                             │
│ 4. Network Data                             │
│    └─ Direct interactions (followers)       │
│    └─ Second-order network                  │
│    └─ Relationship types                    │
│                                             │
├─────────────────────────────────────────────┤
│ OUTPUT: DuckDB with complete data model     │
│ NEXT: Phase 2 (MCP Saturation)              │
└─────────────────────────────────────────────┘
```

---

## Data Sources Details

### 1. Bluesky API (@barton.bluesky)

**What We're Collecting**:
- All posts by @barton
- Timestamps, content, engagement metrics
- All interactions: replies, likes, reposts, quotes
- Network mentions and followers
- Real-time activity stream

**Implementation**:
- Use AT Protocol (Bluesky's protocol)
- Alternative: Firecrawl for profile page scraping
- Cache for performance
- Real-time streaming via PulseMCP

**Expected Data**:
- Posts: ~1000-5000 (estimate)
- Interactions: ~10000-50000 (estimate)
- Network mentions: ~1000-5000 (estimate)

**Dependencies**:
```clojure
[atproto-clojure/client "..."]  ; or firecrawl for scraping
[com.rpl.pulsemcp/client "..."] ; for real-time updates
```

### 2. GitHub Activity (@barton)

**What We're Collecting**:
- All repositories
- Commit history
- Pull requests and reviews
- Issues and discussions
- Collaborators and contributions

**Implementation**:
- GitHub GraphQL API
- Authenticated requests (GitHub token required)
- Pagination for large datasets
- Cache intermediate results

**Expected Data**:
- Repositories: ~50-200
- Commits: ~1000-5000
- PRs/Issues: ~200-1000
- Network collaborators: ~50-500

**Dependencies**:
```clojure
[com.github/graphql-java "..."]
[clj-http "..."]
```

### 3. Firecrawled Web Content

**What We're Collecting**:
- All URLs referenced in barton posts
- Full page content
- Metadata (title, description, author)
- Domain information
- Content categorization

**Implementation**:
- Extract URLs from posts
- Batch firecrawl requests
- Cache content hashes
- Metadata extraction
- Topic classification

**Expected Data**:
- URLs: ~500-2000
- Content pages: ~200-1000
- Average content per page: ~5KB

**Dependencies**:
```clojure
[com.firecrawl/api "..."] ; or firecrawl_scrape MCP tool
```

### 4. Network Data

**What We're Collecting**:
- Direct network (followers, following)
- Second-order network (followers of followers)
- Interaction patterns
- Relationship types
- Influence flows

**Implementation**:
- Build from posts/interactions
- Augment with API data
- Network graph construction
- Centrality analysis
- Community detection

**Expected Data**:
- Direct connections: ~1000-5000
- Second-order: ~10000-50000
- Relationship types: 5-10 (reply, like, mention, follow, etc.)

---

## Implementation Phases

### Phase 1a: Setup (Immediate)

1. **Create Data Acquisition Module**
   - File: `src/agents/data_acquisition.clj`
   - Functions for each data source
   - Error handling and retries
   - Caching layer

2. **Create DuckDB Schema**
   - File: Updated `barton_surrogate_system.clj`
   - All 7 tables defined
   - Indexes for fast queries
   - Constraints and types

3. **Create Data Pipeline**
   - Orchestration of acquisition
   - Progress tracking
   - Data validation
   - Duplicate detection

### Phase 1b: Bluesky Data (Depends on API access)

1. Authenticate with Bluesky/AT Protocol
2. Fetch all @barton posts (paginated)
3. Fetch post interactions (replies, likes, etc.)
4. Fetch network data (followers)
5. Normalize and deduplicate
6. Load into DuckDB

**Expected time**: 30-60 minutes (depends on volume)

### Phase 1c: GitHub Data (Requires token)

1. Authenticate with GitHub GraphQL
2. Fetch all repositories
3. Fetch commits, PRs, issues
4. Fetch collaborators and network
5. Normalize data
6. Load into DuckDB

**Expected time**: 15-30 minutes

### Phase 1d: Firecrawled Content (Uses Firecrawl MCP)

1. Extract unique URLs from posts
2. Batch firecrawl requests
3. Parse and extract metadata
4. Categorize content
5. Load into DuckDB

**Expected time**: 30-120 minutes (depends on URL volume)

### Phase 1e: Network Analysis

1. Build network graph from interactions
2. Calculate centrality measures
3. Detect communities
4. Identify influence flows
5. Load network data into DuckDB

**Expected time**: 10-20 minutes

### Phase 1f: Validation & Optimization

1. Validate data completeness
2. Check data quality
3. Create indexes
4. Generate statistics
5. Document data coverage

**Expected time**: 10-15 minutes

---

## DuckDB Schema

```sql
-- Core data tables
CREATE TABLE barton_posts (
  post_id VARCHAR PRIMARY KEY,
  text TEXT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  platform VARCHAR,  -- 'bluesky', 'twitter', etc
  likes INT DEFAULT 0,
  reposts INT DEFAULT 0,
  replies INT DEFAULT 0,
  source_data JSON,
  indexed_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE barton_interactions (
  interaction_id VARCHAR PRIMARY KEY,
  post_id VARCHAR NOT NULL,
  actor_user_id VARCHAR NOT NULL,
  actor_username VARCHAR,
  interaction_type VARCHAR,  -- 'reply', 'like', 'repost', 'quote'
  timestamp TIMESTAMP NOT NULL,
  content TEXT,  -- for replies/quotes
  source_data JSON,
  FOREIGN KEY (post_id) REFERENCES barton_posts(post_id)
);

CREATE TABLE barton_network (
  relationship_id VARCHAR PRIMARY KEY,
  source_user_id VARCHAR NOT NULL,
  source_username VARCHAR,
  target_user_id VARCHAR NOT NULL,
  target_username VARCHAR,
  relationship_type VARCHAR,  -- 'follower', 'following', 'collaborator'
  interaction_count INT DEFAULT 0,
  strength FLOAT DEFAULT 0.5,
  established_at TIMESTAMP,
  source_data JSON
);

CREATE TABLE github_activity (
  activity_id VARCHAR PRIMARY KEY,
  repository_name VARCHAR NOT NULL,
  activity_type VARCHAR,  -- 'commit', 'pr', 'issue', 'review'
  timestamp TIMESTAMP NOT NULL,
  details JSON,
  metadata JSON,
  indexed_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE web_references (
  reference_id VARCHAR PRIMARY KEY,
  original_url VARCHAR NOT NULL,
  domain VARCHAR,
  title TEXT,
  description TEXT,
  content TEXT,
  content_hash VARCHAR,
  mentioned_in_post VARCHAR,
  fetch_timestamp TIMESTAMP,
  metadata JSON,
  FOREIGN KEY (mentioned_in_post) REFERENCES barton_posts(post_id)
);

CREATE TABLE interaction_entropy (
  sequence_id VARCHAR PRIMARY KEY,
  interaction_ids STRUCT[VARCHAR],
  entropy_score FLOAT,
  information_gain FLOAT,
  predictability FLOAT,
  calculated_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE cognitive_profile (
  profile_id VARCHAR PRIMARY KEY,
  profile_data JSON,  -- Values, interests, style
  confidence_score FLOAT,
  last_updated TIMESTAMP,
  version INT
);

-- Create indexes for fast queries
CREATE INDEX idx_posts_created ON barton_posts(created_at);
CREATE INDEX idx_posts_platform ON barton_posts(platform);
CREATE INDEX idx_interactions_post ON barton_interactions(post_id);
CREATE INDEX idx_interactions_actor ON barton_interactions(actor_user_id);
CREATE INDEX idx_network_source ON barton_network(source_user_id);
CREATE INDEX idx_network_target ON barton_network(target_user_id);
CREATE INDEX idx_github_repo ON github_activity(repository_name);
CREATE INDEX idx_web_domain ON web_references(domain);
CREATE INDEX idx_web_post_ref ON web_references(mentioned_in_post);
```

---

## Success Criteria

### Data Completeness
- ✅ All @barton posts acquired
- ✅ All interactions captured
- ✅ Network mapped (direct + 2nd order)
- ✅ GitHub activity complete
- ✅ Web references crawled

### Data Quality
- ✅ No null values in critical fields
- ✅ Timestamps consistent and valid
- ✅ No duplicate records
- ✅ Relationships referentially consistent
- ✅ Text content properly encoded

### Database Quality
- ✅ All tables populated
- ✅ Indexes created and working
- ✅ Query performance <100ms
- ✅ No data corruption
- ✅ Backup created

### Coverage Metrics
- ✅ Posts: 100% of available
- ✅ Interactions: 100% of accessible
- ✅ Network: 100% of connected
- ✅ GitHub: 100% of public
- ✅ Web: 100% of referenced

---

## Key Decisions

### Data Source Priority
1. **High Priority**: Bluesky (primary platform)
2. **High Priority**: Network (enables interperspective analysis)
3. **Medium Priority**: GitHub (shows technical interests)
4. **Medium Priority**: Web (shows information sources)

### Error Handling Strategy
- Retry failed requests (3 attempts)
- Cache intermediate results
- Partial success acceptable (some API limits)
- Log all errors for debugging
- Continue if one source partially fails

### Data Freshness
- **Initial**: Pull all historical data
- **Ongoing**: Real-time updates via PulseMCP
- **Refresh**: Daily batch updates recommended
- **Archiving**: Keep immutable snapshots

---

## Dependencies Required

```clojure
;; Bluesky/AT Protocol
[bluesky-clj "..."]  ; or firecrawl for scraping

;; GitHub
[tentacles "..."]     ; or graphql-java

;; Firecrawl (MCP tool)
[com.firecrawl/client "..."]

;; Database
[com.duckdb/duckdb_java "..."]

;; Data processing
[org.clojure/data.csv "..."]
[cheshire "..."]  ; JSON

;; Network/HTTP
[clj-http "..."]
[aleph "..."]  ; for async

;; Caching
[com.github.ben-manes.caffeine/caffeine "..."]
```

---

## Timeline & Resource Allocation

| Phase | Component | Est. Time | Status |
|-------|-----------|-----------|--------|
| 1a | Setup & Schema | 20 min | Ready to start |
| 1b | Bluesky Data | 30-60 min | Blocked on API |
| 1c | GitHub Data | 15-30 min | Ready (need token) |
| 1d | Web Content | 30-120 min | Ready (using Firecrawl) |
| 1e | Network Data | 10-20 min | Ready |
| 1f | Validation | 10-15 min | Ready |
| **TOTAL** | **Phase 1** | **2-4 hours** | **Ready to start** |

---

## Next: Phase 2 After Phase 1 Complete

Once data is in DuckDB:
- ✅ MCP space saturation (load & index)
- ✅ Create perception layer (all data accessible)
- ✅ Create action layer (all operations available)
- ✅ Measure query performance

---

## Status

```
PHASE 1 READINESS:
├─ Planning: ✅ COMPLETE
├─ Schema Design: ✅ COMPLETE
├─ Data Sources: ✅ IDENTIFIED
├─ Dependencies: ✅ LISTED
├─ Error Handling: ✅ DESIGNED
├─ Timeline: ✅ ESTIMATED
└─ READY TO START: ✅ YES

BLOCKERS:
├─ Bluesky API access: Needs verification
├─ GitHub token: Required before start
├─ @barton username: Assumed = "barton.bluesky"
└─ Data availability: TBD

IMMEDIATE NEXT STEP:
└─ Start Phase 1a (Setup & Schema)
```

---

**Next Action**: Proceed to Phase 1a implementation
