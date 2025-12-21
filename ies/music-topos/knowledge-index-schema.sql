-- DuckDB Knowledge Graph Schema: Roughgarden, a16z, Paradigm, and Ecosystem
-- Designed for maximum awareness of resource materialization
-- Paradigm-vetted Rust ecosystem focus

-- Core resources table
CREATE TABLE IF NOT EXISTS resources (
    resource_id INTEGER PRIMARY KEY,
    title VARCHAR,
    author VARCHAR,
    resource_type VARCHAR, -- 'lecture', 'paper', 'talk', 'report', 'course'
    source_platform VARCHAR, -- 'youtube', 'stanford', 'a16z', 'paradigm', 'arxiv', 'github'
    url VARCHAR UNIQUE,
    published_date DATE,
    last_indexed TIMESTAMP,
    description TEXT,
    duration_minutes INTEGER, -- for videos
    page_count INTEGER, -- for papers
    access_level VARCHAR -- 'public', 'restricted'
);

-- Topic/subject hierarchy
CREATE TABLE IF NOT EXISTS topics (
    topic_id INTEGER PRIMARY KEY,
    topic_name VARCHAR UNIQUE,
    parent_topic_id INTEGER,
    category VARCHAR, -- 'mechanism_design', 'distributed_systems', 'crypto', 'ai', 'music'
    description TEXT
);

-- Resource-topic relationships
CREATE TABLE IF NOT EXISTS resource_topics (
    resource_id INTEGER,
    topic_id INTEGER,
    relevance_score FLOAT, -- 0.0-1.0
    PRIMARY KEY (resource_id, topic_id)
);

-- Content structure (for courses/series)
CREATE TABLE IF NOT EXISTS content_sequence (
    sequence_id INTEGER PRIMARY KEY,
    parent_resource_id INTEGER,
    sequence_number INTEGER,
    title VARCHAR,
    description TEXT,
    url VARCHAR,
    duration_minutes INTEGER,
    published_date DATE
);

-- Key concepts and definitions
CREATE TABLE IF NOT EXISTS concepts (
    concept_id INTEGER PRIMARY KEY,
    concept_name VARCHAR UNIQUE,
    formal_definition TEXT,
    intuitive_explanation TEXT,
    mathematical_notation VARCHAR,
    first_introduced_in INTEGER -- resource_id
);

-- Concept relationships
CREATE TABLE IF NOT EXISTS concept_relationships (
    concept_from_id INTEGER,
    concept_to_id INTEGER,
    relationship_type VARCHAR, -- 'requires', 'extends', 'contradicts', 'exemplifies'
    strength FLOAT,
    PRIMARY KEY (concept_from_id, concept_to_id)
);

-- Rust library ecosystem (paradigm-vetted)
CREATE TABLE IF NOT EXISTS rust_crates (
    crate_id INTEGER PRIMARY KEY,
    crate_name VARCHAR UNIQUE,
    description TEXT,
    paradigm_vetted BOOLEAN, -- Has it been verified as high-quality?
    domain VARCHAR, -- 'audio', 'distributed', 'crypto', 'data', 'parallelism'
    maturity_level VARCHAR, -- 'experimental', 'stable', 'production'
    github_url VARCHAR,
    crates_io_url VARCHAR,
    stars_on_github INTEGER,
    last_updated DATE,
    quality_score FLOAT -- 0.0-100.0
);

-- Research threads (connecting multiple resources)
CREATE TABLE IF NOT EXISTS research_threads (
    thread_id INTEGER PRIMARY KEY,
    thread_name VARCHAR,
    description TEXT,
    core_question TEXT,
    created_date DATE,
    updated_date DATE
);

-- Thread participants
CREATE TABLE IF NOT EXISTS thread_resources (
    thread_id INTEGER,
    resource_id INTEGER,
    position_in_thread INTEGER,
    contribution_type VARCHAR, -- 'foundational', 'extending', 'critiquing', 'synthesis'
    PRIMARY KEY (thread_id, resource_id)
);

-- Speaker/Author profiles
CREATE TABLE IF NOT EXISTS speakers (
    speaker_id INTEGER PRIMARY KEY,
    name VARCHAR UNIQUE,
    affiliation VARCHAR,
    expertise_areas VARCHAR[], -- array of topics
    recent_work_url VARCHAR,
    publications_count INTEGER,
    h_index INTEGER,
    focus_area TEXT
);

-- Relationships between speakers
CREATE TABLE IF NOT EXISTS speaker_collaborations (
    speaker_1_id INTEGER,
    speaker_2_id INTEGER,
    collaboration_count INTEGER,
    latest_collaboration_date DATE,
    PRIMARY KEY (speaker_1_id, speaker_2_id)
);

-- Bridge table: connecting music-topos concepts to external knowledge
CREATE TABLE IF NOT EXISTS knowledge_bridges (
    bridge_id INTEGER PRIMARY KEY,
    music_topos_concept VARCHAR, -- e.g., 'color_generation', 'determinism', 'parallelism'
    external_resource_id INTEGER,
    connection_type VARCHAR, -- 'theoretical_foundation', 'implementation_pattern', 'mathematical_basis'
    relevance_text TEXT,
    created_date DATE
);

-- Implementation tracking (for Rust gay.rs integration)
CREATE TABLE IF NOT EXISTS implementation_mapping (
    mapping_id INTEGER PRIMARY KEY,
    gay_rs_component VARCHAR, -- e.g., 'ColorGenerator', 'MusicalScale', 'MCP_Server'
    theoretical_foundation_resource_id INTEGER,
    rust_crate_id INTEGER,
    implementation_status VARCHAR, -- 'planned', 'in_progress', 'complete'
    notes TEXT,
    updated_date DATE
);

-- Index for fast queries
CREATE INDEX idx_resources_type ON resources(resource_type);
CREATE INDEX idx_resources_author ON resources(author);
CREATE INDEX idx_topics_category ON topics(category);
CREATE INDEX idx_concepts_name ON concepts(concept_name);
CREATE INDEX idx_rust_domain ON rust_crates(domain);
CREATE INDEX idx_speakers_expertise ON speakers(expertise_areas);
CREATE INDEX idx_thread_question ON research_threads(core_question);

-- Views for materialization and awareness

-- All Roughgarden resources indexed
CREATE VIEW roughgarden_resources AS
SELECT
    resource_id,
    title,
    resource_type,
    published_date,
    url,
    description
FROM resources
WHERE author ILIKE '%Roughgarden%'
ORDER BY published_date DESC;

-- All a16z crypto research
CREATE VIEW a16z_research AS
SELECT
    resource_id,
    title,
    resource_type,
    published_date,
    url,
    description
FROM resources
WHERE source_platform = 'a16z'
ORDER BY published_date DESC;

-- State machine replication learning path
CREATE VIEW smr_learning_path AS
SELECT
    rt.resource_id,
    r.title,
    r.author,
    r.resource_type,
    cs.sequence_number,
    r.url
FROM resources r
JOIN resource_topics rt ON r.resource_id = rt.resource_id
JOIN topics t ON rt.topic_id = t.topic_id
LEFT JOIN content_sequence cs ON r.resource_id = cs.parent_resource_id
WHERE t.topic_name ILIKE '%state machine%'
   OR t.topic_name ILIKE '%replication%'
   OR t.topic_name ILIKE '%consensus%'
ORDER BY r.published_date DESC, cs.sequence_number ASC;

-- Mechanism design curriculum
CREATE VIEW mechanism_design_curriculum AS
SELECT
    cs.sequence_id,
    cs.sequence_number,
    cs.title,
    cs.duration_minutes,
    r.author,
    r.published_date,
    cs.url,
    cs.description
FROM content_sequence cs
JOIN resources r ON cs.parent_resource_id = r.resource_id
WHERE r.title ILIKE '%mechanism%'
   OR r.title ILIKE '%auction%'
   OR r.title ILIKE '%incentive%'
ORDER BY r.published_date DESC, cs.sequence_number ASC;

-- Paradigm-vetted Rust ecosystem map
CREATE VIEW vetted_rust_ecosystem AS
SELECT
    rc.crate_name,
    rc.domain,
    rc.maturity_level,
    rc.quality_score,
    rc.github_url,
    rc.description
FROM rust_crates rc
WHERE rc.paradigm_vetted = true
ORDER BY rc.domain, rc.quality_score DESC;

-- Knowledge bridges (theory to implementation)
CREATE VIEW theory_to_implementation AS
SELECT
    kb.music_topos_concept,
    r.title AS theoretical_resource,
    rc.crate_name AS rust_implementation,
    kb.connection_type,
    kb.relevance_text
FROM knowledge_bridges kb
JOIN resources r ON kb.external_resource_id = r.resource_id
LEFT JOIN implementation_mapping im ON kb.music_topos_concept = im.gay_rs_component
LEFT JOIN rust_crates rc ON im.rust_crate_id = rc.crate_id;

-- Research thread map
CREATE VIEW research_map AS
SELECT
    rt.thread_name,
    rt.core_question,
    COUNT(DISTINCT tr.resource_id) AS resource_count,
    MIN(tr2.position_in_thread) AS foundational_position,
    rt.updated_date
FROM research_threads rt
JOIN thread_resources tr ON rt.thread_id = tr.thread_id
LEFT JOIN thread_resources tr2 ON rt.thread_id = tr2.thread_id
    AND tr2.contribution_type = 'foundational'
GROUP BY rt.thread_id, rt.thread_name, rt.core_question, rt.updated_date
ORDER BY resource_count DESC;
