# Materialization Layer Design
## Resource Discovery + Awareness System

**Date**: 2025-12-21
**Purpose**: Transform the knowledge graph into actionable discovery and awareness mechanisms
**Integration**: Bridges knowledge-indexer (DuckDB) with gay.rs (semantic colors) and music-topos

---

## 1. Overview: From Data to Discovery

The materialization layer bridges two worlds:
- **Input**: Raw knowledge graph from indexer (1256 resources, 186 topics, 342 people)
- **Output**: Materialized views, discovery recommendations, awareness surfaces

```
DuckDB Knowledge Graph
    ↓
Materialization Engine
    ├─ Topic Clustering
    ├─ Path Recommendations
    ├─ Expert Ranking
    ├─ Expertise Gaps
    ├─ Opportunity Maps
    ├─ Learning Progressions
    └─ Awareness Surfaces
    ↓
Resource Discovery
    ├─ Interactive Browser
    ├─ Semantic Search
    ├─ Color-Coded Browsing
    ├─ Recommendation Engine
    ├─ Learning Pathways
    └─ Expertise Profiles
```

---

## 2. Core Materialization Components

### 2.1 Topic Clustering & Relationships

**Problem**: 186 topics without structure is overwhelming
**Solution**: Compute topic clusters and relationship strength

```sql
-- Compute topic co-occurrence networks
CREATE VIEW v_topic_clusters AS
WITH topic_pairs AS (
    SELECT DISTINCT
        rt1.topic_id as topic_1,
        rt2.topic_id as topic_2,
        COUNT(DISTINCT rt1.resource_id) as co_occurrence_count
    FROM resource_topics rt1
    JOIN resource_topics rt2
        ON rt1.resource_id = rt2.resource_id
        AND rt1.topic_id < rt2.topic_id
    GROUP BY rt1.topic_id, rt2.topic_id
    HAVING COUNT(DISTINCT rt1.resource_id) >= 3
)
SELECT
    t1.topic_name as topic_1_name,
    t2.topic_name as topic_2_name,
    co_occurrence_count,
    ROUND(co_occurrence_count::float / NULLIF(MIN(
        (SELECT COUNT(*) FROM resource_topics WHERE topic_id = topic_1),
        (SELECT COUNT(*) FROM resource_topics WHERE topic_id = topic_2)
    ), 0), 3) as jaccard_similarity
FROM topic_pairs
JOIN topics t1 ON topic_pairs.topic_1 = t1.id
JOIN topics t2 ON topic_pairs.topic_2 = t2.id
ORDER BY co_occurrence_count DESC;
```

### 2.2 Learning Path Generation

**Problem**: Students don't know optimal learning sequence
**Solution**: Generate personalized paths through knowledge graph

```sql
-- Generate recommended learning paths
CREATE VIEW v_learning_recommendations AS
WITH difficulty_scores AS (
    SELECT
        t.id as topic_id,
        t.topic_name,
        COUNT(DISTINCT r.id) as resource_count,
        AVG(rr.difficulty_level) as avg_difficulty,
        AVG(rr.clarity_score) as avg_clarity,
        COUNT(DISTINCT tp.prerequisite_topic_id) as prerequisite_count
    FROM topics t
    LEFT JOIN resource_topics rt ON t.id = rt.topic_id
    LEFT JOIN resources r ON rt.resource_id = r.id
    LEFT JOIN resource_ratings rr ON r.id = rr.resource_id
    LEFT JOIN topic_prerequisites tp ON t.id = tp.dependent_topic_id
    GROUP BY t.id, t.topic_name
)
SELECT
    topic_id,
    topic_name,
    ROUND(avg_difficulty::numeric, 2) as difficulty,
    ROUND(avg_clarity::numeric, 2) as clarity,
    prerequisite_count,
    resource_count,
    CASE
        WHEN prerequisite_count = 0 AND avg_difficulty < 3 THEN 'foundation'
        WHEN prerequisite_count <= 1 AND avg_difficulty < 4 THEN 'intermediate'
        WHEN prerequisite_count >= 2 OR avg_difficulty >= 4 THEN 'advanced'
        ELSE 'specialized'
    END as learning_level
FROM difficulty_scores
ORDER BY difficulty, prerequisite_count;
```

### 2.3 Expert Ranking & Authority

**Problem**: Hard to identify who's truly authoritative on a topic
**Solution**: Compute expertise scores using multiple signals

```sql
-- Compute expertise scores
CREATE VIEW v_expert_authority AS
WITH author_stats AS (
    SELECT
        p.id,
        p.name,
        t.id as topic_id,
        t.topic_name,
        COUNT(DISTINCT r.id) as publication_count,
        AVG(r.page_rank_score) as avg_influence,
        MAX(r.publication_date) as latest_publication,
        EXTRACT(YEAR FROM MAX(r.publication_date))::int -
        EXTRACT(YEAR FROM MIN(r.publication_date))::int as years_active,
        ROUND(
            COUNT(DISTINCT r.id)::float /
            (SELECT COUNT(*) FROM resource_authors ra2
             WHERE ra2.author_id = p.id),
            2
        ) as publication_concentration
    FROM people p
    JOIN resource_authors ra ON p.id = ra.author_id
    JOIN resources r ON ra.resource_id = r.id
    JOIN resource_topics rt ON r.id = rt.resource_id
    JOIN topics t ON rt.topic_id = t.id
    WHERE rt.relevance_score >= 0.7
    GROUP BY p.id, p.name, t.id, t.topic_name
)
SELECT
    name,
    topic_name,
    publication_count,
    ROUND(avg_influence::numeric, 3) as influence_score,
    years_active,
    publication_concentration,
    ROUND(
        (publication_count::float / NULLIF(years_active, 0)) +
        (avg_influence * 0.5) +
        (publication_concentration * 0.3),
        2
    ) as authority_score,
    CASE
        WHEN publication_count >= 20 AND avg_influence > 0.7 THEN 'thought_leader'
        WHEN publication_count >= 10 AND avg_influence > 0.6 THEN 'established_researcher'
        WHEN publication_count >= 5 THEN 'active_contributor'
        ELSE 'emerging_voice'
    END as authority_tier
FROM author_stats
WHERE publication_count >= 3
ORDER BY authority_score DESC;
```

### 2.4 Knowledge Gap Detection

**Problem**: What areas are under-served?
**Solution**: Identify gaps in coverage and opportunity areas

```sql
-- Find knowledge gaps
CREATE VIEW v_knowledge_gaps AS
SELECT
    t.topic_name,
    t.category,
    COUNT(DISTINCT rt.resource_id) as resource_coverage,
    COUNT(DISTINCT ra.author_id) as author_coverage,
    EXTRACT(YEAR FROM MAX(r.publication_date)) as latest_year,
    CASE
        WHEN COUNT(DISTINCT rt.resource_id) <= 1 THEN 'critical_gap'
        WHEN COUNT(DISTINCT rt.resource_id) <= 3 THEN 'significant_gap'
        WHEN COUNT(DISTINCT rt.resource_id) <= 5 THEN 'minor_gap'
        WHEN EXTRACT(YEAR FROM MAX(r.publication_date)) < 2023 THEN 'stale_content'
        ELSE 'well_covered'
    END as coverage_status,
    ROUND(
        100.0 * COUNT(DISTINCT rt.resource_id) /
        (SELECT MAX(resource_count) FROM (
            SELECT COUNT(*) as resource_count FROM resource_topics GROUP BY topic_id
        )),
        1
    ) as percentile_coverage
FROM topics t
LEFT JOIN resource_topics rt ON t.id = rt.topic_id
LEFT JOIN resources r ON rt.resource_id = r.id
LEFT JOIN resource_authors ra ON r.id = ra.resource_id
GROUP BY t.id, t.topic_name, t.category
HAVING COUNT(DISTINCT rt.resource_id) <= 5
   OR EXTRACT(YEAR FROM MAX(r.publication_date)) < 2023
ORDER BY resource_coverage ASC;
```

### 2.5 Topic Dependency Tree

**Problem**: Hard to see prerequisites
**Solution**: Compute and visualize dependency chains

```sql
-- Build prerequisite chains
CREATE VIEW v_topic_prerequisites_expanded AS
WITH RECURSIVE prereq_chain AS (
    -- Base: topics with no prerequisites
    SELECT
        id,
        topic_name,
        category,
        1 as depth,
        ARRAY[id] as path,
        ARRAY[topic_name] as name_path
    FROM topics
    WHERE id NOT IN (SELECT dependent_topic_id FROM topic_prerequisites)

    UNION ALL

    -- Recursive: topics with prerequisites
    SELECT
        tp.dependent_topic_id,
        t.topic_name,
        t.category,
        pc.depth + 1,
        ARRAY_PREPEND(tp.prerequisite_topic_id, pc.path),
        ARRAY_PREPEND(pt.topic_name, pc.name_path)
    FROM topic_prerequisites tp
    JOIN topics t ON tp.dependent_topic_id = t.id
    JOIN topics pt ON tp.prerequisite_topic_id = pt.id
    JOIN prereq_chain pc ON tp.prerequisite_topic_id = pc.id
    WHERE ARRAY_LENGTH(pc.path, 1) < 10  -- Prevent infinite recursion
)
SELECT
    id as topic_id,
    topic_name,
    category,
    depth as prerequisite_depth,
    name_path as prerequisite_chain,
    ARRAY_TO_STRING(name_path, ' ← ') as readable_path
FROM prereq_chain
WHERE depth > 1  -- Only show topics with prerequisites
ORDER BY depth DESC, topic_name;
```

---

## 3. Awareness Surfaces

### 3.1 Dashboard View

```sql
-- Materialized dashboard for overview
CREATE VIEW v_dashboard_snapshot AS
SELECT
    (SELECT COUNT(*) FROM resources) as total_resources,
    (SELECT COUNT(*) FROM people) as total_experts,
    (SELECT COUNT(*) FROM topics) as total_topics,
    (SELECT COUNT(*) FROM topics WHERE category = 'consensus') as consensus_topics,
    (SELECT COUNT(*) FROM topics WHERE category = 'cryptography') as crypto_topics,
    (SELECT COUNT(*) FROM topics WHERE category = 'mechanism_design') as mechanism_topics,
    (SELECT AVG(page_rank_score) FROM resources) as avg_resource_quality,
    (SELECT COUNT(*) FROM resources WHERE publication_date >= CURRENT_DATE - INTERVAL '6 months') as recent_resources,
    (SELECT COUNT(*) FROM topics WHERE id IN (SELECT topic_id FROM v_knowledge_gaps)) as gap_topics;
```

### 3.2 Recommendation Engine

**Query**: "I'm interested in consensus. What should I learn next?"

```sql
-- Personalized learning recommendations
CREATE FUNCTION recommend_next_topics(
    interested_in_topic_id INT,
    current_level VARCHAR,
    limit_count INT DEFAULT 5
)
RETURNS TABLE (
    recommended_topic_id INT,
    topic_name VARCHAR,
    reason VARCHAR,
    difficulty_level VARCHAR,
    resource_count INT
) AS $$
    WITH related_topics AS (
        SELECT DISTINCT
            tc.topic_2_id as related_id,
            t2.topic_name,
            tc.connection_strength,
            'Directly related' as reason
        FROM topic_connections tc
        JOIN topics t2 ON tc.topic_2_id = t2.id
        WHERE tc.topic_1_id = interested_in_topic_id
            AND tc.connection_strength > 0.5

        UNION ALL

        SELECT DISTINCT
            tp.dependent_topic_id as related_id,
            t3.topic_name,
            1.0 - (ABS(rr.difficulty_level -
                (SELECT AVG(rr2.difficulty_level)
                 FROM resource_ratings rr2
                 JOIN resources r2 ON rr2.resource_id = r2.id
                 JOIN resource_topics rt2 ON r2.id = rt2.resource_id
                 WHERE rt2.topic_id = interested_in_topic_id)) / 5.0) as connection_strength,
            'Builds on this topic' as reason
        FROM topic_prerequisites tp
        JOIN topics t3 ON tp.dependent_topic_id = t3.id
        LEFT JOIN resource_ratings rr ON rr.resource_id IS NOT NULL
        WHERE tp.prerequisite_topic_id = interested_in_topic_id
            AND tp.dependent_topic_id != interested_in_topic_id
    )
    SELECT
        related_topics.related_id,
        related_topics.topic_name,
        related_topics.reason,
        lr.learning_level,
        (SELECT COUNT(*) FROM resource_topics WHERE topic_id = related_topics.related_id)
    FROM related_topics
    LEFT JOIN v_learning_recommendations lr
        ON related_topics.related_id = lr.topic_id
    WHERE lr.learning_level != current_level  -- Suggest different level
    ORDER BY connection_strength DESC
    LIMIT limit_count;
$$ LANGUAGE SQL;
```

### 3.3 Discovery Feed

```sql
-- Fresh resources for discovery
CREATE VIEW v_discovery_feed AS
SELECT
    r.title,
    r.url,
    p.name as contributor,
    t.topic_name,
    r.publication_date,
    r.resource_type,
    r.duration_minutes,
    r.page_rank_score,
    'new_resource' as discovery_type
FROM resources r
LEFT JOIN resource_authors ra ON r.id = ra.resource_id
LEFT JOIN people p ON ra.author_id = p.id
LEFT JOIN resource_topics rt ON r.id = rt.resource_id
LEFT JOIN topics t ON rt.topic_id = t.id
WHERE r.publication_date >= CURRENT_DATE - INTERVAL '30 days'
ORDER BY r.publication_date DESC, r.page_rank_score DESC
LIMIT 50;
```

---

## 4. Integration with Gay.rs

### 4.1 Topic-to-Color Mapping

Each topic gets a deterministic color from the golden angle spiral:

```
Consensus Topics (10) → Hues 0-70°
  ├─ Byzantine Consensus → Hue 0°
  ├─ Tendermint → Hue 13.75°
  ├─ Proof-of-Stake → Hue 27.5°
  └─ ... (7 more)

Cryptography Topics (12) → Hues 70-160°
  ├─ Zero-Knowledge Proofs → Hue 70°
  ├─ Elliptic Curves → Hue 83.75°
  └─ ...

Mechanism Design Topics (8) → Hues 160-250°
  └─ ...
```

**Implementation**:
```rust
// gay-rs integration
let category_hue_base = match topic.category {
    TopicCategory::Consensus => 0.0,
    TopicCategory::Cryptography => 70.0,
    TopicCategory::MechanismDesign => 160.0,
    // ... more categories
};

let topic_color = {
    let hue = (category_hue_base + (topic_index % 13) * 13.75) % 360.0;
    OkhslColor {
        hue,
        saturation: 0.5 + (popularity * 0.5),  // Popular = more saturated
        lightness: 0.3 + (coverage * 0.4),     // Well-covered = brighter
    }
};
```

### 4.2 Learning Paths as Music

Each learning path is sonified:
- **Topic Progression** → **Melodic Progression** (hues → pitches)
- **Topic Difficulty** → **Register/Octave** (lightness → octave)
- **Topic Centrality** → **Amplitude** (authority → volume)

---

## 5. Deployment Architecture

### 5.1 Layered System

```
┌────────────────────────────────────────┐
│     Web Interface / API Layer          │
│  (Browser discovery, semantic search)  │
├────────────────────────────────────────┤
│   Materialization Views Layer          │
│  (Expert ranking, learning paths, gaps)│
├────────────────────────────────────────┤
│     DuckDB Knowledge Graph             │
│  (Resources, people, topics, relations)│
├────────────────────────────────────────┤
│    Content Indexer (Rust)              │
│  (Crawling, parsing, enrichment)       │
├────────────────────────────────────────┤
│   Original Sources                     │
│  (Roughgarden, a16z, Paradigm, etc.)   │
└────────────────────────────────────────┘
```

### 5.2 Refresh Cycle

```
Hourly:
  ├─ Crawl new resources from known sources
  ├─ Validate URL accessibility
  └─ Add to DuckDB

Daily:
  ├─ Recompute topic clusters
  ├─ Update expert rankings
  ├─ Detect knowledge gaps
  └─ Generate learning recommendations

Weekly:
  ├─ Deep citation analysis
  ├─ Topic trend detection
  ├─ Author influence updates
  └─ Learning path optimization

Monthly:
  ├─ Schema optimization
  ├─ Archive old content metadata
  ├─ Generate research reports
  └─ Backup database
```

---

## 6. Example Use Cases

### Use Case 1: New Learner Path

**User**: "I want to learn about Byzantine Fault Tolerance"

**System Response** (using materialization):
1. Find "Byzantine Consensus" topic (hue = 0°, color = red)
2. Get prerequisites from `v_topic_prerequisites_expanded`
3. Recommend foundational resources from `v_learning_recommendations`
4. Display top 3 experts from `v_expert_authority`
5. Show related topics from `recommend_next_topics()`
6. Provide reading sequence with estimated time

**Color Representation**:
```
Foundation (lightness: 0.4) → dark red
  ↓ Musical transition
Intermediate (lightness: 0.6) → bright red
  ↓
Advanced (lightness: 0.8) → light red
```

### Use Case 2: Research Opportunity Discovery

**Query**: "What's under-served in DeFi?"

**System Response**:
1. List DeFi topics with `coverage_status = 'critical_gap'`
2. Show gap timeframe from `v_knowledge_gaps`
3. Display who could contribute (authors in adjacent fields)
4. Calculate market opportunity (resource demand vs. supply)

### Use Case 3: Expert Collaboration Suggestion

**Query**: "I'm working on MEV. Who should I connect with?"

**System Response**:
1. Find co-authors of MEV papers
2. Find experts in related topics
3. Compute collaboration strength scores
4. Suggest complementary expertise gaps

---

## 7. Success Metrics

### Coverage
- [ ] 80%+ of resources properly indexed (topics + authors)
- [ ] <5% orphaned resources (no topics, no authors)
- [ ] Dependency chains accurately represented

### Discovery
- [ ] Users find 3+ relevant resources per session
- [ ] 70%+ of discovered resources rated relevant
- [ ] Learning paths reduce discovery time by 50%

### Authority
- [ ] Expert ranking correlates with citations (r² > 0.7)
- [ ] Authority scores stable across 3-month window
- [ ] Emerging voices identified before 100 publications

### Gaps
- [ ] Identified gaps resolve within 6 months → opportunity validation
- [ ] Gap detection prevents "knowledge redundancy"
- [ ] Guides new content creation

---

## 8. Files Created

1. **MATERIALIZATION_LAYER_DESIGN.md** - This document
2. **MATERIALIZATION_QUERIES.sql** - All view definitions
3. **materialization-service/** - Rust service for computing materializations
4. **web-interface/** - React dashboard for discovery

---

## Closing Philosophy

> "The knowledge graph exists to serve discovery, not to be discovered itself."

The materialization layer transforms raw interconnected data into actionable awareness. Each view, each recommendation, each color-coded surface exists to answer one question:

**"What should I learn next?"**

The answers flow through golden-ratio-spiraled colors, through musical progressions, through personalized pathways—all grounded in the topology of human knowledge itself.
