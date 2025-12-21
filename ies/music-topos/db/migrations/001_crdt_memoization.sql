-- =============================================================================
-- CRDT Memoization Temporal Database Schema
-- DuckDB + Time-Travel Semantics
-- =============================================================================
--
-- Implements 3-layer memoization:
-- Layer 1: DuckDB Temporal Versioning (freeze/recover pattern)
-- Layer 2: Content-Addressed Merge Cache (fingerprint-based)
-- Layer 3: Egg E-Graph Verification (equality saturation)
--
-- Time-travel recovery via snapshot mechanism:
--   recover_crdt_state(crdt_id, timestamp) → state at that moment
--

-- =============================================================================
-- Table 1: CRDT Operations Log (Append-Only)
-- =============================================================================
--
-- Event-sourced log of all CRDT operations.
-- Each op has: (site_id, counter, operation, payload, vector_clock)
--

CREATE TABLE IF NOT EXISTS crdt_operations (
    op_id BIGINT DEFAULT nextval('crdt_operations_seq'),
    site_id VARCHAR NOT NULL,          -- Agent ID
    counter BIGINT NOT NULL,           -- Logical timestamp
    crdt_type VARCHAR NOT NULL,        -- TextCRDT, JSONCRDT, GCounter, etc.
    operation VARCHAR NOT NULL,        -- insert, delete, merge, increment, etc.
    payload JSON NOT NULL,             -- Operation-specific data
    vector_clock JSON NOT NULL,        -- {agent_id → logical_clock}
    fingerprint BIGINT NOT NULL,       -- FNV-1a content hash
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY (op_id),
    UNIQUE (site_id, counter)          -- Causally ordered
);

CREATE SEQUENCE IF NOT EXISTS crdt_operations_seq;
CREATE INDEX IF NOT EXISTS idx_crdt_ops_site_id ON crdt_operations(site_id);
CREATE INDEX IF NOT EXISTS idx_crdt_ops_timestamp ON crdt_operations(timestamp);
CREATE INDEX IF NOT EXISTS idx_crdt_ops_fingerprint ON crdt_operations(fingerprint);

-- =============================================================================
-- Table 2: CRDT Snapshots (Freeze-Fork-State)
-- =============================================================================
--
-- Periodic snapshots of CRDT state for deterministic recovery.
-- Follows parallel_color_fork.clj freeze pattern.
--
-- To recover state at time T:
--   SELECT state FROM crdt_snapshots
--   WHERE crdt_id = ? AND frozen_at <= ?
--   ORDER BY frozen_at DESC LIMIT 1
--

CREATE TABLE IF NOT EXISTS crdt_snapshots (
    snapshot_id VARCHAR PRIMARY KEY,
    crdt_id VARCHAR NOT NULL,
    crdt_type VARCHAR NOT NULL,
    state JSON NOT NULL,               -- Full CRDT state
    vector_clock JSON NOT NULL,
    fingerprint BIGINT NOT NULL,
    frozen_at TIMESTAMP NOT NULL,
    parent_snapshot VARCHAR,           -- Snapshot lineage
    agent_id VARCHAR NOT NULL,         -- Agent that created snapshot
    FOREIGN KEY (parent_snapshot) REFERENCES crdt_snapshots(snapshot_id)
);

CREATE INDEX IF NOT EXISTS idx_crdt_snaps_id ON crdt_snapshots(crdt_id);
CREATE INDEX IF NOT EXISTS idx_crdt_snaps_frozen ON crdt_snapshots(frozen_at);
CREATE INDEX IF NOT EXISTS idx_crdt_snaps_fp ON crdt_snapshots(fingerprint);

-- =============================================================================
-- Table 3: Content-Addressed Merge Cache (Layer 2 Memoization)
-- =============================================================================
--
-- Caches expensive merge operations by content hash.
-- Key: (left_fingerprint, right_fingerprint, operation)
-- Result: Cached merged state + vector clock
--
-- Cache hit ratio target: 70-90% for typical workloads
-- Staleness detection: Vector clock comparison
--

CREATE TABLE IF NOT EXISTS merge_cache (
    cache_id VARCHAR PRIMARY KEY,
    left_fingerprint BIGINT NOT NULL,
    right_fingerprint BIGINT NOT NULL,
    operation VARCHAR NOT NULL,        -- 'join', 'union', etc.
    result_fingerprint BIGINT NOT NULL,
    result_state JSON NOT NULL,
    result_vector_clock JSON NOT NULL,
    polarity VARCHAR DEFAULT 'neutral', -- positive/negative/neutral (Girard)
    hit_count BIGINT DEFAULT 0,
    miss_count BIGINT DEFAULT 0,
    computed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    invalidated_at TIMESTAMP          -- NULL = valid, timestamp = stale
);

CREATE INDEX IF NOT EXISTS idx_merge_cache_key ON merge_cache(left_fingerprint, right_fingerprint, operation);
CREATE INDEX IF NOT EXISTS idx_merge_cache_result ON merge_cache(result_fingerprint);
CREATE INDEX IF NOT EXISTS idx_merge_cache_polarity ON merge_cache(polarity);

-- =============================================================================
-- Table 4: Möbius Invalidation Cascade
-- =============================================================================
--
-- Tracks cache invalidation dependencies for Möbius lattice propagation.
-- When a CRDT is modified, invalidates all dependent merge cache entries.
--

CREATE TABLE IF NOT EXISTS cache_dependencies (
    dependency_id VARCHAR PRIMARY KEY,
    source_fingerprint BIGINT NOT NULL,
    target_cache_id VARCHAR NOT NULL,
    cascade_depth BIGINT NOT NULL DEFAULT 1,
    invalidated_at TIMESTAMP,
    FOREIGN KEY (target_cache_id) REFERENCES merge_cache(cache_id)
);

CREATE INDEX IF NOT EXISTS idx_cache_deps_source ON cache_dependencies(source_fingerprint);
CREATE INDEX IF NOT EXISTS idx_cache_deps_target ON cache_dependencies(target_cache_id);

-- =============================================================================
-- Table 5: Vector Clock Tracking (Causality)
-- =============================================================================
--
-- Stores vector clocks for staleness detection.
-- Used by cache lookup to determine if cached state is valid.
--

CREATE TABLE IF NOT EXISTS vector_clocks (
    vc_id VARCHAR PRIMARY KEY,
    crdt_id VARCHAR NOT NULL,
    clocks JSON NOT NULL,              -- {agent_id → logical_clock}
    recorded_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    is_causally_after_previous BOOLEAN DEFAULT TRUE
);

CREATE INDEX IF NOT EXISTS idx_vc_crdt_id ON vector_clocks(crdt_id);
CREATE INDEX IF NOT EXISTS idx_vc_recorded ON vector_clocks(recorded_at);

-- =============================================================================
-- Table 6: Lazy Evaluation Queue
-- =============================================================================
--
-- On-demand computation tasks for parallel processing.
-- Processes batch merges, saturation, verification in background.
--

CREATE TABLE IF NOT EXISTS lazy_queue (
    task_id VARCHAR PRIMARY KEY,
    task_type VARCHAR NOT NULL,        -- 'merge', 'saturate', 'verify'
    priority BIGINT DEFAULT 0,         -- Lower = higher priority
    crdt_id VARCHAR,
    left_crdt VARCHAR,
    right_crdt VARCHAR,
    payload JSON,
    status VARCHAR DEFAULT 'pending',  -- pending/in_progress/completed/failed
    started_at TIMESTAMP,
    completed_at TIMESTAMP,
    result JSON,
    error_message VARCHAR
);

CREATE INDEX IF NOT EXISTS idx_lazy_status ON lazy_queue(status);
CREATE INDEX IF NOT EXISTS idx_lazy_priority ON lazy_queue(priority);

-- =============================================================================
-- Table 7: Egg E-Graph Equality Classes (Layer 3 Verification)
-- =============================================================================
--
-- Tracks e-graph equality saturation for CRDT verification.
-- Used by Phase 2 to verify merge commutativity via egg e-graphs.
--

CREATE TABLE IF NOT EXISTS egg_eclasses (
    eclass_id VARCHAR PRIMARY KEY,
    canonical_term JSON NOT NULL,
    equivalent_terms JSON NOT NULL,    -- Alternative representations
    proof_graph JSON,                  -- Saturation proof DAG
    vector_clock JSON NOT NULL,
    crdt_type VARCHAR,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_egg_eclass_crdt ON egg_eclasses(crdt_type);

-- =============================================================================
-- Table 8: Ramanujan Agent Coordination (Phase 3 Preparation)
-- =============================================================================
--
-- Tracks state of 9-agent distributed system.
-- Agents: indexed 0-8 (3×3 Ramanujan expander topology)
--

CREATE TABLE IF NOT EXISTS agent_state (
    agent_id VARCHAR PRIMARY KEY,
    mathematician VARCHAR NOT NULL,    -- Agent personality (Ramanujan, Grothendieck, etc.)
    polarity VARCHAR,                  -- positive/negative/neutral
    sierpinski_address VARCHAR,        -- Hierarchical address in Sierpinski gasket
    last_heartbeat TIMESTAMP,
    vector_clock JSON,
    pending_operations BIGINT DEFAULT 0,
    processed_operations BIGINT DEFAULT 0,
    cache_hits BIGINT DEFAULT 0,
    cache_misses BIGINT DEFAULT 0
);

CREATE INDEX IF NOT EXISTS idx_agent_heartbeat ON agent_state(last_heartbeat);

-- =============================================================================
-- Recovery Functions (Deterministic State Reconstruction)
-- =============================================================================
--

-- Recover CRDT state at specific point in time
CREATE FUNCTION recover_crdt_state(
    p_crdt_id VARCHAR,
    p_timestamp TIMESTAMP
) RETURNS JSON AS $$
    SELECT state FROM crdt_snapshots
    WHERE crdt_id = $1 AND frozen_at <= $2
    ORDER BY frozen_at DESC LIMIT 1
$$ LANGUAGE SQL IMMUTABLE;

-- Reconstruct CRDT from operations log
CREATE FUNCTION reconstruct_from_ops(
    p_crdt_id VARCHAR,
    p_up_to_op_id BIGINT
) RETURNS JSON AS $$
    WITH ops AS (
        SELECT payload, operation
        FROM crdt_operations
        WHERE site_id = $1 AND op_id <= $2
        ORDER BY op_id
    )
    SELECT json_object_agg(operation, count(*)) FROM ops
$$ LANGUAGE SQL IMMUTABLE;

-- Get all cache hits for statistics
CREATE FUNCTION cache_hit_rate() RETURNS DECIMAL AS $$
    SELECT SUM(hit_count)::DECIMAL /
           (SUM(hit_count) + SUM(miss_count))
    FROM merge_cache
    WHERE hit_count + miss_count > 0
$$ LANGUAGE SQL IMMUTABLE;

-- =============================================================================
-- Triggers (Automatic Maintenance)
-- =============================================================================
--

-- Invalidate dependent caches when CRDT updated
CREATE TRIGGER invalidate_cache_on_update
AFTER INSERT ON crdt_operations
FOR EACH ROW
BEGIN
    UPDATE merge_cache
    SET invalidated_at = CURRENT_TIMESTAMP
    WHERE left_fingerprint = NEW.fingerprint
       OR right_fingerprint = NEW.fingerprint;
END;

-- =============================================================================
-- Initial Data (9 Agents - Ramanujan Combinatorial Complex)
-- =============================================================================
--

INSERT OR IGNORE INTO agent_state (agent_id, mathematician, polarity, sierpinski_address)
VALUES
    ('agent_0', 'Ramanujan', 'positive', '000'),
    ('agent_1', 'Grothendieck', 'neutral', '010'),
    ('agent_2', 'Euler', 'negative', '020'),
    ('agent_3', 'de Paiva', 'neutral', '100'),
    ('agent_4', 'Hedges', 'positive', '110'),
    ('agent_5', 'Girard', 'negative', '120'),
    ('agent_6', 'Spivak', 'positive', '200'),
    ('agent_7', 'Lawvere', 'neutral', '210'),
    ('agent_8', 'Scholze', 'negative', '220');

-- =============================================================================
-- Views (Query Helpers)
-- =============================================================================
--

-- Active cache entries (not invalidated)
CREATE VIEW active_merge_cache AS
    SELECT * FROM merge_cache
    WHERE invalidated_at IS NULL;

-- Agent health status
CREATE VIEW agent_health AS
    SELECT
        agent_id,
        mathematician,
        (CURRENT_TIMESTAMP - last_heartbeat) AS last_heartbeat_ago,
        cache_hits + cache_misses AS total_ops,
        CASE WHEN cache_hits + cache_misses > 0
             THEN cache_hits::DECIMAL / (cache_hits + cache_misses)
             ELSE 0 END AS hit_rate
    FROM agent_state;

-- Recent snapshots by CRDT
CREATE VIEW recent_snapshots AS
    SELECT
        crdt_id,
        MAX(frozen_at) AS latest_snapshot,
        COUNT(*) AS snapshot_count
    FROM crdt_snapshots
    GROUP BY crdt_id;

-- =============================================================================
-- End Schema
-- =============================================================================
