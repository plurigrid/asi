-- DuckDB Schema for Content Indexing and Knowledge Graph
-- Designed to organize Tim Roughgarden, a16z Crypto, and Paradigm Research content
-- Build date: 2025-12-21
-- Purpose: Enable semantic search, relationship discovery, and materialization

-- ============================================================================
-- CORE ENTITIES
-- ============================================================================

-- Resources: The primary unit (lectures, papers, talks, blog posts, etc.)
CREATE TABLE resources (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    resource_type VARCHAR NOT NULL,  -- 'lecture', 'paper', 'talk', 'blog_post', 'video', 'course'
    title VARCHAR NOT NULL,
    description TEXT,
    url VARCHAR UNIQUE NOT NULL,
    source VARCHAR NOT NULL,  -- 'roughgarden', 'a16z_crypto', 'paradigm', 'stanford', 'columbia', 'youtube'
    publication_date DATE,
    last_updated TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    duration_minutes INTEGER,  -- For videos/lectures
    is_accessible BOOLEAN DEFAULT TRUE,  -- Track if URL is still valid
    page_rank_score FLOAT DEFAULT 0.5,  -- For importance ranking
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- People: Authors, speakers, researchers
CREATE TABLE people (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    name VARCHAR NOT NULL UNIQUE,
    affiliation VARCHAR,  -- Stanford, Columbia, a16z, Paradigm, etc.
    role VARCHAR,  -- Professor, Researcher, Speaker, Author
    bio TEXT,
    twitter_handle VARCHAR,
    website_url VARCHAR,
    is_prominent BOOLEAN DEFAULT FALSE,
    relevance_score FLOAT DEFAULT 0.5
);

-- Topics/Concepts: The main subject areas
CREATE TABLE topics (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    topic_name VARCHAR NOT NULL UNIQUE,
    category VARCHAR NOT NULL,  -- 'consensus', 'cryptography', 'game_theory', 'mechanism_design', 'distributed_systems', 'defi', 'zk_proofs'
    description TEXT,
    parent_topic_id INTEGER REFERENCES topics(id),  -- For hierarchical topics
    level INTEGER DEFAULT 0  -- Nesting level in hierarchy
);

-- Courses/Series: Group related lectures
CREATE TABLE course_series (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    course_name VARCHAR NOT NULL UNIQUE,
    instructor_id INTEGER REFERENCES people(id),
    institution VARCHAR,  -- Stanford, Columbia
    year INTEGER,
    semester VARCHAR,  -- Spring, Fall, etc.
    course_number VARCHAR,  -- CS364A, etc.
    total_lectures INTEGER,
    description TEXT,
    website_url VARCHAR
);

-- ============================================================================
-- RELATIONSHIPS
-- ============================================================================

-- Author/Speaker contributions
CREATE TABLE resource_authors (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    author_id INTEGER NOT NULL REFERENCES people(id) ON DELETE CASCADE,
    role VARCHAR DEFAULT 'author',  -- 'author', 'speaker', 'co-author'
    position_order INTEGER,  -- Order of authorship
    UNIQUE(resource_id, author_id)
);

-- Resource to topic mapping (many-to-many)
CREATE TABLE resource_topics (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    topic_id INTEGER NOT NULL REFERENCES topics(id) ON DELETE CASCADE,
    relevance_score FLOAT DEFAULT 0.5,  -- 0-1, how central is this topic to the resource
    UNIQUE(resource_id, topic_id)
);

-- Course membership: Which lectures belong to which courses
CREATE TABLE course_lectures (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    course_id INTEGER NOT NULL REFERENCES course_series(id) ON DELETE CASCADE,
    resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    lecture_number INTEGER NOT NULL,  -- Sequence in course
    UNIQUE(course_id, resource_id)
);

-- Citation relationships: One resource references another
CREATE TABLE citations (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    citing_resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    cited_resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    citation_context TEXT,  -- Brief description of how it's cited
    citation_type VARCHAR DEFAULT 'general',  -- 'builds_on', 'extends', 'contradicts', 'validates'
    UNIQUE(citing_resource_id, cited_resource_id)
);

-- Prerequisites: Learning dependencies
CREATE TABLE prerequisites (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    dependent_resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    prerequisite_resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    importance VARCHAR DEFAULT 'recommended',  -- 'required', 'recommended', 'helpful'
    UNIQUE(dependent_resource_id, prerequisite_resource_id)
);

-- Topic prerequisites: Conceptual dependencies
CREATE TABLE topic_prerequisites (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    dependent_topic_id INTEGER NOT NULL REFERENCES topics(id) ON DELETE CASCADE,
    prerequisite_topic_id INTEGER NOT NULL REFERENCES topics(id) ON DELETE CASCADE,
    UNIQUE(dependent_topic_id, prerequisite_topic_id)
);

-- ============================================================================
-- ANNOTATIONS & METADATA
-- ============================================================================

-- Key concepts extracted from resources (for semantic search)
CREATE TABLE resource_concepts (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    concept_name VARCHAR NOT NULL,
    concept_definition TEXT,
    first_mentioned_at INTEGER,  -- Lecture number or timestamp
    importance_score FLOAT DEFAULT 0.5  -- 0-1, how central to the resource
);

-- Timestamps within lectures (chapters/sections)
CREATE TABLE lecture_chapters (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    chapter_number INTEGER,
    chapter_title VARCHAR,
    start_time_seconds INTEGER,
    end_time_seconds INTEGER,
    topic_ids JSON,  -- Array of topic IDs covered
    description TEXT
);

-- Tags for flexible categorization
CREATE TABLE resource_tags (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    tag VARCHAR NOT NULL,
    tag_category VARCHAR DEFAULT 'general',  -- 'difficulty', 'application', 'methodology'
    UNIQUE(resource_id, tag)
);

-- Peer reviews and ratings
CREATE TABLE resource_ratings (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    rating_score FLOAT,  -- 1-5
    rating_count INTEGER DEFAULT 1,
    difficulty_level INTEGER,  -- 1-5
    clarity_score FLOAT,  -- 1-5
    relevance_to_paradigm FLOAT,  -- 1-5, how relevant to paradigm research
    last_reviewed DATE
);

-- ============================================================================
-- KNOWLEDGE GRAPH ANALYSIS
-- ============================================================================

-- Computed topic relationships (from citation analysis)
CREATE TABLE topic_connections (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    topic_1_id INTEGER NOT NULL REFERENCES topics(id) ON DELETE CASCADE,
    topic_2_id INTEGER NOT NULL REFERENCES topics(id) ON DELETE CASCADE,
    connection_strength FLOAT,  -- 0-1, based on co-citation frequency
    connection_type VARCHAR,  -- 'related', 'prerequisite', 'applications', 'theory_practice'
    evidence_count INTEGER DEFAULT 0,  -- How many resources connect these topics
    UNIQUE(topic_1_id, topic_2_id)
);

-- Learning paths: Recommended sequences through material
CREATE TABLE learning_paths (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    path_name VARCHAR NOT NULL UNIQUE,
    description TEXT,
    target_outcome VARCHAR,  -- What should learner understand
    difficulty_level VARCHAR,  -- 'beginner', 'intermediate', 'advanced'
    estimated_hours FLOAT,
    created_date DATE DEFAULT CURRENT_DATE
);

-- Resources in learning paths
CREATE TABLE learning_path_resources (
    id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
    learning_path_id INTEGER NOT NULL REFERENCES learning_paths(id) ON DELETE CASCADE,
    resource_id INTEGER NOT NULL REFERENCES resources(id) ON DELETE CASCADE,
    sequence_number INTEGER NOT NULL,
    time_estimate_hours FLOAT,
    notes TEXT  -- Why this resource at this point
);

-- ============================================================================
-- QUERYING VIEWS
-- ============================================================================

-- View: Resources with all metadata
CREATE VIEW v_resources_full AS
SELECT
    r.id,
    r.resource_type,
    r.title,
    r.url,
    r.source,
    r.publication_date,
    r.duration_minutes,
    STRING_AGG(DISTINCT p.name, ', ') AS authors,
    STRING_AGG(DISTINCT t.topic_name, ', ') AS topics,
    STRING_AGG(DISTINCT t.category, ', ') AS categories,
    r.page_rank_score,
    r.created_at
FROM resources r
LEFT JOIN resource_authors ra ON r.id = ra.resource_id
LEFT JOIN people p ON ra.author_id = p.id
LEFT JOIN resource_topics rt ON r.id = rt.resource_id
LEFT JOIN topics t ON rt.topic_id = t.id
GROUP BY r.id, r.resource_type, r.title, r.url, r.source, r.publication_date, r.duration_minutes, r.page_rank_score, r.created_at;

-- View: Topic hierarchy
CREATE VIEW v_topic_hierarchy AS
WITH RECURSIVE topic_tree AS (
    -- Base case: root topics (no parent)
    SELECT
        id,
        topic_name,
        category,
        parent_topic_id,
        level,
        CAST(topic_name AS VARCHAR) AS path
    FROM topics
    WHERE parent_topic_id IS NULL

    UNION ALL

    -- Recursive case: child topics
    SELECT
        t.id,
        t.topic_name,
        t.category,
        t.parent_topic_id,
        t.level,
        CONCAT(tt.path, ' > ', t.topic_name)
    FROM topics t
    JOIN topic_tree tt ON t.parent_topic_id = tt.id
)
SELECT * FROM topic_tree
ORDER BY path;

-- View: Most relevant resources for each topic
CREATE VIEW v_topic_resources_ranked AS
SELECT
    t.topic_name,
    t.category,
    r.title,
    r.resource_type,
    r.source,
    rt.relevance_score,
    r.publication_date,
    ROW_NUMBER() OVER (PARTITION BY t.id ORDER BY rt.relevance_score DESC, r.publication_date DESC) AS rank_in_topic
FROM topics t
JOIN resource_topics rt ON t.id = rt.topic_id
JOIN resources r ON rt.resource_id = r.id
WHERE rt.relevance_score >= 0.5;

-- View: Citation network
CREATE VIEW v_citation_network AS
SELECT
    r1.id AS source_resource_id,
    r1.title AS source_title,
    r1.source AS source_source,
    r2.id AS cited_resource_id,
    r2.title AS cited_title,
    r2.source AS cited_source,
    c.citation_type,
    c.citation_context
FROM citations c
JOIN resources r1 ON c.citing_resource_id = r1.id
JOIN resources r2 ON c.cited_resource_id = r2.id;

-- ============================================================================
-- ANALYTICAL QUERIES (as stored procedures/functions)
-- ============================================================================

-- Query: Find prerequisites for a topic
CREATE VIEW v_learning_chain AS
WITH RECURSIVE deps AS (
    -- Starting topics (no prerequisites)
    SELECT
        t.id,
        t.topic_name,
        1 AS depth,
        ARRAY[t.id] AS path_ids,
        ARRAY[t.topic_name] AS path_names
    FROM topics t
    WHERE NOT EXISTS (
        SELECT 1 FROM topic_prerequisites WHERE dependent_topic_id = t.id
    )

    UNION ALL

    -- Dependent topics
    SELECT
        tp.dependent_topic_id AS id,
        t.topic_name,
        deps.depth + 1,
        ARRAY_APPEND(deps.path_ids, t.id),
        ARRAY_APPEND(deps.path_names, t.topic_name)
    FROM topic_prerequisites tp
    JOIN deps ON tp.prerequisite_topic_id = deps.id
    JOIN topics t ON tp.dependent_topic_id = t.id
)
SELECT * FROM deps;

-- Query: Find experts in a topic
CREATE VIEW v_topic_experts AS
SELECT
    t.topic_name,
    p.name AS expert,
    p.affiliation,
    COUNT(DISTINCT r.id) AS resource_count,
    AVG(rt.relevance_score) AS avg_relevance,
    MAX(r.publication_date) AS most_recent_work
FROM topics t
JOIN resource_topics rt ON t.id = rt.topic_id
JOIN resources r ON rt.resource_id = r.id
JOIN resource_authors ra ON r.id = ra.resource_id
JOIN people p ON ra.author_id = p.id
WHERE rt.relevance_score >= 0.6
GROUP BY t.id, t.topic_name, p.id, p.name, p.affiliation
ORDER BY resource_count DESC, avg_relevance DESC;

-- ============================================================================
-- INDEXES FOR PERFORMANCE
-- ============================================================================

CREATE INDEX idx_resources_source ON resources(source);
CREATE INDEX idx_resources_type ON resources(resource_type);
CREATE INDEX idx_resources_date ON resources(publication_date DESC);
CREATE INDEX idx_resource_topics_resource ON resource_topics(resource_id);
CREATE INDEX idx_resource_topics_topic ON resource_topics(topic_id);
CREATE INDEX idx_resource_authors_resource ON resource_authors(resource_id);
CREATE INDEX idx_resource_authors_person ON resource_authors(author_id);
CREATE INDEX idx_citations_citing ON citations(citing_resource_id);
CREATE INDEX idx_citations_cited ON citations(cited_resource_id);
CREATE INDEX idx_topics_category ON topics(category);
CREATE INDEX idx_course_lectures_course ON course_lectures(course_id);
CREATE INDEX idx_topic_connections_topic1 ON topic_connections(topic_1_id);
CREATE INDEX idx_topic_connections_topic2 ON topic_connections(topic_2_id);

-- ============================================================================
-- BOOTSTRAP DATA LOADING UTILITIES
-- ============================================================================

-- Function to calculate PageRank-style importance scores
-- (Would be called periodically to update page_rank_score in resources)
-- SELECT calculate_resource_importance() -- Not yet implemented

-- Function to detect new topics from resource annotations
-- SELECT extract_topics_from_resources() -- Not yet implemented

-- ============================================================================
-- EXAMPLE QUERIES
-- ============================================================================

-- Find all resources about consensus mechanisms
-- SELECT * FROM v_resources_full WHERE topics LIKE '%consensus%';

-- Find learning path from Foundations to Advanced Mechanism Design
-- SELECT * FROM v_learning_chain WHERE topic_name LIKE '%mechanism%';

-- Find who works on zero-knowledge proofs and their latest work
-- SELECT * FROM v_topic_experts WHERE topic_name LIKE '%zero-knowledge%';

-- Find resources that cite Tim Roughgarden's Byzantine work
-- SELECT citing_resource_id, COUNT(*) as times_cited FROM citations
-- WHERE cited_resource_id IN (SELECT id FROM resources WHERE title LIKE '%Byzantine%')
-- GROUP BY citing_resource_id;

-- Find topic clusters (topics often discussed together)
-- SELECT t1.topic_name, t2.topic_name, tc.connection_strength
-- FROM topic_connections tc
-- JOIN topics t1 ON tc.topic_1_id = t1.id
-- JOIN topics t2 ON tc.topic_2_id = t2.id
-- WHERE tc.connection_strength > 0.7
-- ORDER BY tc.connection_strength DESC;

-- ============================================================================
-- NOTES
-- ============================================================================
-- This schema is designed to:
-- 1. Index Tim Roughgarden lectures, a16z crypto talks, and Paradigm research
-- 2. Create a knowledge graph with topics, people, and relationships
-- 3. Support semantic search and discovery
-- 4. Enable learning path recommendation
-- 5. Track expertise and authority
-- 6. Support citation analysis and impact metrics
--
-- Integration points:
-- - Connects to gay.rs for music-topos bridging (future)
-- - Supports materialization layer for resource awareness
-- - Can be queried via Rust crawler for automatic indexing
-- ============================================================================
