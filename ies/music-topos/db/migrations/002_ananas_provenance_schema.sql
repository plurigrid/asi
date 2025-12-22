-- Ananas-Music-Topos Provenance Schema
-- Tracks complete genealogy of composition artifacts
-- Created: 2025-12-21

-- ============================================================================
-- 1. ARTIFACT REGISTRY (Master table)
-- ============================================================================

CREATE TABLE IF NOT EXISTS artifact_provenance (
    artifact_id VARCHAR PRIMARY KEY,
    artifact_type VARCHAR NOT NULL,  -- 'composition' | 'proof' | 'analysis' | 'history'
    github_interaction_id VARCHAR,
    content_hash VARCHAR NOT NULL,   -- SHA3-256 hash
    gayseed_index INTEGER NOT NULL,  -- 0-11 (maps to rainbow color)
    gayseed_hex VARCHAR,             -- e.g., '#aa00ff'
    creation_timestamp TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    last_updated TIMESTAMP DEFAULT CURRENT_TIMESTAMP,

    -- Metadata
    researchers_involved JSON,       -- ["user1", "user2", ...]
    artifact_metadata JSON,          -- Type-specific metadata
    is_verified BOOLEAN DEFAULT FALSE,
    verification_timestamp TIMESTAMP
);

-- ============================================================================
-- 2. PROVENANCE NODES (ACSet objects)
-- ============================================================================

CREATE TABLE IF NOT EXISTS provenance_nodes (
    artifact_id VARCHAR NOT NULL,
    node_type VARCHAR NOT NULL,      -- 'Query' | 'MD5' | 'File' | 'Witness' | 'Doc'
    sequence_order INTEGER NOT NULL,  -- Order in pipeline

    -- Generic JSON storage for node data
    node_data JSON NOT NULL,

    -- Node-specific fields
    query_id VARCHAR,                -- For Query nodes
    md5_hash VARCHAR,                -- For MD5 nodes
    file_path VARCHAR,               -- For File nodes
    file_size BIGINT,                -- File size in bytes
    witness_proof_id VARCHAR,        -- For Witness nodes
    doc_export_format VARCHAR,       -- For Doc nodes (json|markdown|lean4|pdf)

    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,

    FOREIGN KEY (artifact_id) REFERENCES artifact_provenance(artifact_id),
    PRIMARY KEY (artifact_id, sequence_order)
);

-- ============================================================================
-- 3. PROVENANCE MORPHISMS (ACSet arrows)
-- ============================================================================

CREATE TABLE IF NOT EXISTS provenance_morphisms (
    artifact_id VARCHAR NOT NULL,
    source_node_type VARCHAR NOT NULL,
    target_node_type VARCHAR NOT NULL,
    morphism_label VARCHAR NOT NULL,  -- 'search' | 'download' | 'attest' | 'convert'

    -- Morphism properties
    is_verified BOOLEAN DEFAULT FALSE,
    verification_method VARCHAR,      -- e.g., 'lean4_proof'
    morphism_data JSON,

    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,

    FOREIGN KEY (artifact_id) REFERENCES artifact_provenance(artifact_id),
    PRIMARY KEY (artifact_id, source_node_type, target_node_type)
);

-- ============================================================================
-- 4. 3-PARTITE CONNECTIONS (Machine → User → Shared)
-- ============================================================================

CREATE TABLE IF NOT EXISTS tripartite_connections (
    composition_id VARCHAR NOT NULL,

    -- Machine Partition (from color_chain)
    machine_cycle INTEGER,
    battery_level FLOAT,
    machine_timestamp TIMESTAMP,

    -- User Partition (researcher activity)
    user_researcher VARCHAR,
    github_activity_id VARCHAR,
    user_activity_type VARCHAR,      -- 'created' | 'modified' | 'verified'

    -- Shared Partition (artifact)
    shared_artifact_id VARCHAR,
    shared_artifact_type VARCHAR,

    -- Edge information
    edge_type VARCHAR NOT NULL,       -- 'machine→user' | 'user→shared' | 'shared→machine'
    edge_label VARCHAR,               -- 'observation' | 'creation' | 'feedback'
    edge_weight FLOAT DEFAULT 1.0,    -- Strength of connection

    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,

    FOREIGN KEY (composition_id) REFERENCES artifact_provenance(artifact_id),
    FOREIGN KEY (shared_artifact_id) REFERENCES artifact_provenance(artifact_id)
);

-- ============================================================================
-- 5. ARTIFACT EXPORTS (publication tracking)
-- ============================================================================

CREATE TABLE IF NOT EXISTS artifact_exports (
    artifact_id VARCHAR NOT NULL,
    export_format VARCHAR NOT NULL,  -- 'json' | 'markdown' | 'lean4' | 'pdf'
    export_path VARCHAR NOT NULL,
    export_timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,

    file_size BIGINT,
    checksum VARCHAR,                -- SHA3-256 of exported file
    is_archived BOOLEAN DEFAULT FALSE,

    FOREIGN KEY (artifact_id) REFERENCES artifact_provenance(artifact_id),
    PRIMARY KEY (artifact_id, export_format)
);

-- ============================================================================
-- 6. PROVENANCE AUDIT LOG (immutable record)
-- ============================================================================

CREATE TABLE IF NOT EXISTS provenance_audit_log (
    artifact_id VARCHAR NOT NULL,

    action VARCHAR NOT NULL,         -- 'created' | 'hashed' | 'stored' | 'verified' | 'published'
    action_timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    actor VARCHAR,                   -- Who performed the action

    details JSON,                    -- Action-specific details
    status VARCHAR,                  -- 'success' | 'error' | 'pending'
    error_message VARCHAR
);

-- ============================================================================
-- 7. ARTIST TECHNIQUE THEOREMS (for proof artifacts)
-- ============================================================================

CREATE TABLE IF NOT EXISTS artist_theorem_registry (
    artist_name VARCHAR NOT NULL,
    proof_artifact_id VARCHAR NOT NULL,
    theorem_name VARCHAR NOT NULL,

    theorem_statement JSON,          -- Lean4 theorem syntax
    proof_status VARCHAR,            -- 'proven' | 'partial' | 'conjectured'

    -- Proof details
    lean4_proof_lines INTEGER,
    lean4_complexity VARCHAR,        -- 'simple' | 'moderate' | 'complex'
    dependencies JSON,               -- Other theorems this depends on

    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    verified_at TIMESTAMP,

    FOREIGN KEY (proof_artifact_id) REFERENCES artifact_provenance(artifact_id),
    PRIMARY KEY (artist_name, theorem_name, proof_artifact_id)
);

-- ============================================================================
-- 8. COMPOSITION STRUCTURE (for composition artifacts)
-- ============================================================================

CREATE TABLE IF NOT EXISTS composition_structure (
    composition_id VARCHAR PRIMARY KEY,
    composition_artifact_id VARCHAR NOT NULL,

    instrument_count INTEGER NOT NULL,
    phase_count INTEGER NOT NULL,
    total_voices INTEGER,

    instruments JSON,                -- ["Piano", "Violin", "Cello", ...]
    phases JSON,                     -- [{"type": "RED", ...}, ...]
    gestures JSON,                   -- Composition gestures

    duration_seconds FLOAT,
    tempo_bpm INTEGER,

    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,

    FOREIGN KEY (composition_artifact_id) REFERENCES artifact_provenance(artifact_id),
    INDEX idx_comp_artifact (composition_artifact_id)
);

-- ============================================================================
-- 9. ANALYSIS RESULTS (for analysis artifacts)
-- ============================================================================

CREATE TABLE IF NOT EXISTS analysis_results (
    analysis_id VARCHAR PRIMARY KEY,
    analysis_artifact_id VARCHAR NOT NULL,

    researcher_count INTEGER,
    interaction_count INTEGER,

    tao_interactions INTEGER,
    knoroiov_interactions INTEGER,
    gorard_interactions INTEGER,
    cross_interactions INTEGER,

    temporal_alignments INTEGER,
    -- Temporal window in days
    temporal_window_days INTEGER DEFAULT 60,

    theme_clusters JSON,             -- Theme analysis results
    participant_network JSON,        -- Network analysis

    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,

    FOREIGN KEY (analysis_artifact_id) REFERENCES artifact_provenance(artifact_id),
    INDEX idx_analysis_artifact (analysis_artifact_id)
);

-- ============================================================================
-- 10. VIEWS (for convenient querying)
-- ============================================================================

-- Complete provenance chain view
CREATE OR REPLACE VIEW v_artifact_provenance_chain AS
SELECT
    ap.artifact_id,
    ap.artifact_type,
    ap.content_hash,
    ap.gayseed_index,
    ap.gayseed_hex,
    ap.creation_timestamp,
    ap.is_verified,
    COUNT(DISTINCT CASE WHEN pn.node_type = 'Query' THEN pn.node_id END) as query_count,
    COUNT(DISTINCT CASE WHEN pn.node_type = 'MD5' THEN pn.node_id END) as md5_count,
    COUNT(DISTINCT CASE WHEN pn.node_type = 'File' THEN pn.node_id END) as file_count,
    COUNT(DISTINCT CASE WHEN pn.node_type = 'Witness' THEN pn.node_id END) as witness_count,
    COUNT(DISTINCT CASE WHEN pn.node_type = 'Doc' THEN pn.node_id END) as doc_count,
    COUNT(DISTINCT pm.morphism_id) as morphism_count
FROM artifact_provenance ap
LEFT JOIN provenance_nodes pn ON ap.artifact_id = pn.artifact_id
LEFT JOIN provenance_morphisms pm ON ap.artifact_id = pm.artifact_id
GROUP BY ap.artifact_id;

-- 3-Partite connections view
CREATE OR REPLACE VIEW v_tripartite_graph AS
SELECT
    tc.connection_id,
    tc.composition_id,
    tc.machine_cycle,
    tc.battery_level,
    tc.user_researcher,
    tc.shared_artifact_id,
    tc.edge_type,
    tc.edge_label,
    ap.artifact_type,
    ap.gayseed_hex,
    cc.hex_color as machine_color
FROM tripartite_connections tc
LEFT JOIN artifact_provenance ap ON tc.shared_artifact_id = ap.artifact_id
LEFT JOIN color_chain cc ON tc.machine_cycle = cc.cycle;

-- Artifact timeline view
CREATE OR REPLACE VIEW v_artifact_timeline AS
SELECT
    ap.artifact_id,
    ap.artifact_type,
    ap.creation_timestamp,
    pal.action,
    pal.action_timestamp,
    pal.actor,
    pal.status
FROM artifact_provenance ap
LEFT JOIN provenance_audit_log pal ON ap.artifact_id = pal.artifact_id
ORDER BY ap.artifact_id, pal.action_timestamp;

-- Artist theorem overview
CREATE OR REPLACE VIEW v_artist_theorems_summary AS
SELECT
    artist_name,
    COUNT(*) as theorem_count,
    SUM(CASE WHEN proof_status = 'proven' THEN 1 ELSE 0 END) as proven_count,
    SUM(CASE WHEN proof_status = 'partial' THEN 1 ELSE 0 END) as partial_count,
    SUM(CASE WHEN proof_status = 'conjectured' THEN 1 ELSE 0 END) as conjectured_count,
    AVG(lean4_proof_lines) as avg_proof_lines
FROM artist_theorem_registry
GROUP BY artist_name;

-- ============================================================================
-- 11. INDICES FOR PERFORMANCE
-- ============================================================================

CREATE INDEX IF NOT EXISTS idx_gayseed_color ON artifact_provenance(gayseed_hex);
CREATE INDEX IF NOT EXISTS idx_verification_status ON artifact_provenance(is_verified);
CREATE INDEX IF NOT EXISTS idx_node_sequence ON provenance_nodes(artifact_id, sequence_order);
CREATE INDEX IF NOT EXISTS idx_morphism_flow ON provenance_morphisms(source_node_type, target_node_type);
CREATE INDEX IF NOT EXISTS idx_edge_temporal ON tripartite_connections(machine_timestamp);
CREATE INDEX IF NOT EXISTS idx_export_artifact ON artifact_exports(artifact_id);

-- ============================================================================
-- SCHEMA INITIALIZATION COMPLETE
-- ============================================================================

-- DuckDB Provenance System ready for use
