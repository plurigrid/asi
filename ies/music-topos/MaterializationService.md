# Materialization Service Implementation

**Status**: Specification Ready
**Implementation**: Rust (using knowledge-indexer as foundation)
**Database**: DuckDB materialized views + incremental refresh

## Architecture

```
┌──────────────────────────────────────┐
│   Materialization Service (Rust)     │
├──────────────────────────────────────┤
│  Compute Layer                       │
│  ├─ Topic Clustering                │
│  ├─ Learning Path Generation        │
│  ├─ Expert Authority Scoring        │
│  ├─ Gap Detection                   │
│  └─ Trend Analysis                  │
├──────────────────────────────────────┤
│  Refresh Scheduler                   │
│  ├─ Hourly: New resources           │
│  ├─ Daily: Expert scores            │
│  ├─ Weekly: Deep analysis           │
│  └─ Monthly: Optimization           │
├──────────────────────────────────────┤
│  Storage Layer                       │
│  ├─ Materialized Views (DuckDB)     │
│  ├─ Cache (in-memory)               │
│  └─ Indices (fast lookup)           │
├──────────────────────────────────────┤
│  API Layer                           │
│  ├─ REST endpoints                  │
│  ├─ GraphQL schema                  │
│  └─ Server-sent events              │
└──────────────────────────────────────┘
```

## Core Components

### 1. Topic Clustering Engine

**Input**: Knowledge graph with 186 topics and ~4000 resource-topic relationships
**Output**: Topic clusters with similarity scores

```rust
pub async fn compute_topic_clusters(db: &Database) -> Result<Vec<TopicCluster>> {
    // 1. Fetch all topics
    // 2. Compute co-occurrence matrix
    // 3. Apply Jaccard similarity
    // 4. Cluster using hierarchical clustering
    // 5. Assign cluster IDs
    // 6. Store in materialized_topic_clusters table
}

pub struct TopicCluster {
    pub id: String,
    pub name: String,
    pub topics: Vec<(String, f32)>,  // (topic_name, similarity_score)
    pub center_hue: f32,  // From golden angle
    pub category: TopicCategory,
    pub size: usize,
}
```

### 2. Learning Path Engine

**Algorithm**: Topological sort + difficulty leveling + relevance ranking

```rust
pub async fn generate_learning_paths(db: &Database) -> Result<Vec<LearningPath>> {
    // 1. Extract prerequisite graph
    // 2. Detect cycles and resolve
    // 3. Assign difficulty levels
    // 4. Create paths by difficulty progression
    // 5. Rank resources within each path
    // 6. Estimate time commitment
    // 7. Store in learning_path tables
}

pub struct LearningPath {
    pub id: String,
    pub name: String,
    pub description: String,
    pub difficulty: DifficultyLevel,  // Beginner | Intermediate | Advanced | Expert
    pub estimated_hours: f32,
    pub topics: Vec<TopicInPath>,
    pub resources: Vec<ResourceInPath>,
    pub milestones: Vec<Milestone>,
}

pub struct TopicInPath {
    pub topic_id: i64,
    pub topic_name: String,
    pub sequence: u32,
    pub concepts_taught: Vec<String>,
}

pub struct ResourceInPath {
    pub resource_id: i64,
    pub title: String,
    pub sequence: u32,
    pub estimated_hours: f32,
    pub role: ResourceRole,  // Foundation | Explanation | Example | Challenge
}
```

### 3. Expert Authority Scoring

**Signals**:
- Publication count (weighted by recency)
- Citation count and influence
- Expertise concentration (specialization vs. generalist)
- Years active (credibility)
- Co-authorship network (collaboration quality)

```rust
pub async fn compute_expert_authority(db: &Database) -> Result<Vec<ExpertProfile>> {
    // 1. For each person:
    //    a. Count publications by year
    //    b. Compute citation influence (PageRank)
    //    c. Measure specialization (entropy of topic distribution)
    //    d. Calculate collaboration score
    //    e. Combine signals into authority score
    // 2. Rank by authority within each topic
    // 3. Identify thought leaders, established researchers, emerging voices
    // 4. Store in materialized_experts table
}

pub struct ExpertProfile {
    pub person_id: i64,
    pub name: String,
    pub affiliation: Option<String>,
    pub authority_score: f32,  // 0-100
    pub tier: AuthorityTier,   // ThoughtLeader | Established | Contributor | Emerging
    pub topics: Vec<TopicExpertise>,
    pub publication_count: usize,
    pub years_active: u32,
    pub collaboration_network: Vec<String>,  // Co-authors
    pub color: String,  // From golden angle based on authority
}

pub enum AuthorityTier {
    ThoughtLeader,
    EstablishedResearcher,
    ActiveContributor,
    EmergingVoice,
}

pub struct TopicExpertise {
    pub topic_name: String,
    pub publication_count: usize,
    pub relevance_score: f32,  // How central is this topic to their work
    pub years_since_latest: u32,
    pub authority_in_topic: f32,
}
```

### 4. Knowledge Gap Detection

**Methodology**: Coverage analysis + recency checking + expert availability

```rust
pub async fn detect_knowledge_gaps(db: &Database) -> Result<Vec<KnowledgeGap>> {
    // 1. For each topic:
    //    a. Count resources (coverage)
    //    b. Check publication dates (recency)
    //    c. Count expert contributors
    //    d. Classify gap severity
    // 2. Prioritize by:
    //    a. Demand (how many resources link to this?)
    //    b. Centrality (how many prerequisites depend on this?)
    //    c. Freshness (how old is the latest resource?)
    // 3. Generate recommendations for content creators
}

pub struct KnowledgeGap {
    pub topic_id: i64,
    pub topic_name: String,
    pub category: TopicCategory,
    pub severity: GapSeverity,  // Critical | Significant | Minor | Stale
    pub resource_count: usize,
    pub author_count: usize,
    pub years_since_latest: u32,
    pub opportunity_score: f32,  // How valuable to fill this gap
    pub suggested_keywords: Vec<String>,
}

pub enum GapSeverity {
    CriticalGap,       // 0-1 resources
    SignificantGap,    // 2-3 resources
    MinorGap,          // 4-5 resources
    StaleContent,      // >5 resources but >3 years old
    WellCovered,
}
```

### 5. Color-Based Awareness System

**Integration with gay.rs**:

```rust
pub async fn compute_topic_colors(db: &Database) -> Result<Vec<ColoredTopic>> {
    // 1. Get all topics
    // 2. Assign base hue by category (golden angle partitioning)
    // 3. Adjust saturation by popularity (how many resources)
    // 4. Adjust lightness by coverage (how well-served)
    // 5. Use gay.rs color generation for consistency
}

pub struct ColoredTopic {
    pub topic_id: i64,
    pub topic_name: String,
    pub hue: f32,         // 0-360°
    pub saturation: f32,  // 0-1 (popularity)
    pub lightness: f32,   // 0-1 (coverage)
    pub hex_color: String,
    pub rgb: (u8, u8, u8),
    pub category_group: u32,  // Which golden-angle partition
}

pub async fn compute_learning_path_sonification(
    db: &Database,
    path: &LearningPath
) -> Result<MusicalProgression> {
    // Map learning path to musical progression:
    // - Topic sequence → Melodic progression
    // - Difficulty increase → Register increase
    // - Resource concentration → Harmonic density
    // - Time gap between topics → Rest or transition

    MusicalProgression {
        path_id: path.id.clone(),
        hue_progression: vec![],  // Hues in sequence
        pitch_sequence: vec![],   // Corresponding pitches
        duration: 0,
        tempo_markings: vec![],
        style: MusicalStyle::Educational,
    }
}
```

## Refresh Strategies

### Hourly Refresh
```rust
pub async fn hourly_refresh(db: &Database) -> Result<()> {
    // 1. Fetch new resources from indexer
    // 2. Update accessibility flags
    // 3. Refresh affected expert scores (only those with new publications)
    // 4. Update recent resource rankings
    // 5. Compute incremental changes
    // Time budget: <5 minutes
}
```

### Daily Refresh
```rust
pub async fn daily_refresh(db: &Database) -> Result<()> {
    // 1. Recompute all expert authority scores
    // 2. Regenerate learning paths
    // 3. Update gap detection
    // 4. Compute topic clusters (if threshold of changes exceeded)
    // 5. Cache materialized views
    // Time budget: <30 minutes
}
```

### Weekly Deep Analysis
```rust
pub async fn weekly_deep_refresh(db: &Database) -> Result<()> {
    // 1. Full citation analysis (PageRank)
    // 2. Topic trend detection
    // 3. Emerging researcher identification
    // 4. Collaboration network analysis
    // 5. Learning path optimization
    // 6. Generate research insights
    // Time budget: <2 hours
}
```

## API Layer

### REST Endpoints

```rust
// Discovery API
GET  /api/v1/topics?category=consensus → ColoredTopic[]
GET  /api/v1/topic/:id/learn → LearningPath
GET  /api/v1/topic/:id/experts → ExpertProfile[]
GET  /api/v1/gaps → KnowledgeGap[]
GET  /api/v1/discover?interests=byzantine,consensus → Resource[]
GET  /api/v1/recommend/:person_id → LearningPath[]
GET  /api/v1/trending → TrendingTopic[]

// Expert API
GET  /api/v1/expert/:id → ExpertProfile
GET  /api/v1/expert/:id/collaborators → ExpertProfile[]
GET  /api/v1/expert/:id/publications → Resource[]

// Learning API
GET  /api/v1/path/:id → LearningPath
POST /api/v1/path/:id/start → LearningSession
GET  /api/v1/path/:id/progress → ProgressSnapshot
GET  /api/v1/path/:id/music → MusicalProgression

// Stats API
GET  /api/v1/stats/knowledge-graph → KnowledgeGraphStats
GET  /api/v1/stats/coverage → CoverageStats
GET  /api/v1/stats/trends → TrendStats
```

### WebSocket for Real-time Updates

```rust
// Subscribe to new resources
ws://localhost:8080/ws/updates?topics=consensus,cryptography

// Updates sent as:
{
  "type": "new_resource",
  "resource": {...},
  "related_topics": [...]
}
```

## Testing & Validation

### Unit Tests
- Topic clustering accuracy (similarity scores)
- Path generation (no cycles, valid sequences)
- Expert authority stability (same results with same data)
- Gap detection (matches manual inspection)

### Integration Tests
- Full refresh cycle completes within budget
- Incremental refresh produces same results as full
- API endpoints return expected schema
- Concurrent requests handled correctly

### Validation Rules
- No orphaned topics (every topic ≥ 1 resource)
- No broken prerequisites (dependency DAG is valid)
- Expert scores in [0, 100]
- Learning paths have <3 hour variance in duration

## Performance Targets

| Operation | Time Budget | Current Est. |
|-----------|------------|--------------|
| Topic clustering | <5 min | ~2 min |
| Path generation | <10 min | ~3 min |
| Expert scoring | <15 min | ~8 min |
| Gap detection | <5 min | ~1 min |
| Full daily refresh | <30 min | ~15 min |
| API query latency | <500ms | <100ms |

## Success Criteria

✅ **Completeness**: 95%+ of resources properly categorized
✅ **Freshness**: Expert scores updated daily
✅ **Usefulness**: 70%+ of recommended resources rated relevant
✅ **Performance**: API responses <500ms
✅ **Reliability**: 99.9% uptime of materialization service
✅ **Innovation**: Gap detection accurately predicts future needs

---

## Integration Timeline

1. **Week 1**: Deploy Materialization Service, compute initial views
2. **Week 2**: Integrate with Gay.rs for color assignment
3. **Week 3**: Build Web API and discovery interface
4. **Week 4**: Launch public discovery platform
5. **Month 2**: Add advanced features (sonification, trend detection)
6. **Month 3**: Academic partnership integrations

---

*"The materialization layer makes knowledge discoverable by transforming relationships into awareness."*
