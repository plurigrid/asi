-- APT Detector Observations Schema
-- Stores parallel file observations for semantic differencing analysis
-- Tracks changes over time to detect flickers and ghost files

-- ═══════════════════════════════════════════════════════════════════════════
-- CORE TABLES
-- ═══════════════════════════════════════════════════════════════════════════

CREATE TABLE IF NOT EXISTS observed_files (
    file_id VARCHAR PRIMARY KEY,
    path VARCHAR NOT NULL UNIQUE,
    first_seen TIMESTAMP DEFAULT current_timestamp,
    last_seen TIMESTAMP DEFAULT current_timestamp,
    observation_count INTEGER DEFAULT 0
);

CREATE TABLE IF NOT EXISTS observations (
    observation_id VARCHAR PRIMARY KEY,
    file_id VARCHAR REFERENCES observed_files(file_id),
    timestamp TIMESTAMP DEFAULT current_timestamp,
    method VARCHAR NOT NULL,  -- nio, stat-cmd, ls-cmd, mdls, xattr, getfileinfo
    trit INTEGER NOT NULL,    -- GF(3) assignment: -1, 0, +1
    
    -- Core metadata
    exists BOOLEAN,
    size BIGINT,
    inode BIGINT,
    mtime VARCHAR,
    atime VARCHAR,
    ctime VARCHAR,
    
    -- Extended metadata
    mode VARCHAR,
    uid INTEGER,
    gid INTEGER,
    nlink INTEGER,
    
    -- Spotlight metadata
    spotlight_size VARCHAR,
    spotlight_modified VARCHAR,
    
    -- Extended attributes
    xattr_count INTEGER,
    has_provenance BOOLEAN,
    has_quarantine BOOLEAN,
    
    -- Observation metadata
    elapsed_us INTEGER,
    error VARCHAR
);

CREATE TABLE IF NOT EXISTS anomalies (
    anomaly_id VARCHAR PRIMARY KEY,
    file_id VARCHAR REFERENCES observed_files(file_id),
    detected_at TIMESTAMP DEFAULT current_timestamp,
    anomaly_type VARCHAR NOT NULL,  -- size-mismatch, inode-mismatch, existence-mismatch, spotlight-stale, flicker, ghost
    severity VARCHAR DEFAULT 'medium',  -- low, medium, high, critical
    
    -- Details
    expected_value VARCHAR,
    observed_value VARCHAR,
    methods_involved VARCHAR[],  -- Which observation methods detected discrepancy
    
    -- Resolution
    resolved BOOLEAN DEFAULT FALSE,
    resolved_at TIMESTAMP,
    resolution_notes VARCHAR
);

CREATE TABLE IF NOT EXISTS ghost_files (
    ghost_id VARCHAR PRIMARY KEY,
    directory VARCHAR NOT NULL,
    file_path VARCHAR NOT NULL,
    detected_at TIMESTAMP DEFAULT current_timestamp,
    
    -- Visibility
    visible_to_nio BOOLEAN,
    visible_to_ls BOOLEAN,
    visible_to_find BOOLEAN,
    visible_to_stat BOOLEAN,
    
    -- Classification
    ghost_type VARCHAR,  -- nio-only, ls-only, find-only, missing-from-*
    is_resolved BOOLEAN DEFAULT FALSE
);

CREATE TABLE IF NOT EXISTS flickers (
    flicker_id VARCHAR PRIMARY KEY,
    file_id VARCHAR REFERENCES observed_files(file_id),
    detected_at TIMESTAMP DEFAULT current_timestamp,
    window_start TIMESTAMP,
    window_end TIMESTAMP,
    
    -- Flicker details
    field VARCHAR NOT NULL,  -- size, inode, mtime, etc.
    values_observed VARCHAR[],
    observation_count INTEGER,
    
    -- Analysis
    is_suspicious BOOLEAN DEFAULT FALSE,
    notes VARCHAR
);

-- ═══════════════════════════════════════════════════════════════════════════
-- GF(3) TRIPARTITE TRACKING
-- ═══════════════════════════════════════════════════════════════════════════

CREATE TABLE IF NOT EXISTS observation_triplets (
    triplet_id VARCHAR PRIMARY KEY,
    file_id VARCHAR REFERENCES observed_files(file_id),
    timestamp TIMESTAMP DEFAULT current_timestamp,
    
    -- The three observations
    minus_observation_id VARCHAR REFERENCES observations(observation_id),
    ergodic_observation_id VARCHAR REFERENCES observations(observation_id),
    plus_observation_id VARCHAR REFERENCES observations(observation_id),
    
    -- Conservation check
    trit_sum INTEGER,
    gf3_conserved BOOLEAN,  -- Computed at insert time
    
    -- Semantic consistency
    size_consistent BOOLEAN,
    inode_consistent BOOLEAN,
    existence_consistent BOOLEAN
);

-- ═══════════════════════════════════════════════════════════════════════════
-- VIEWS
-- ═══════════════════════════════════════════════════════════════════════════

-- Latest observation per file per method
CREATE OR REPLACE VIEW latest_observations AS
SELECT DISTINCT ON (file_id, method)
    file_id, method, trit, timestamp, size, inode, mtime, exists
FROM observations
ORDER BY file_id, method, timestamp DESC;

-- Anomaly summary by type
CREATE OR REPLACE VIEW anomaly_summary AS
SELECT 
    anomaly_type,
    severity,
    COUNT(*) as count,
    COUNT(*) FILTER (WHERE NOT resolved) as unresolved,
    MIN(detected_at) as first_detected,
    MAX(detected_at) as last_detected
FROM anomalies
GROUP BY anomaly_type, severity
ORDER BY count DESC;

-- Files with unresolved anomalies
CREATE OR REPLACE VIEW suspicious_files AS
SELECT 
    f.path,
    COUNT(a.anomaly_id) as anomaly_count,
    LIST(DISTINCT a.anomaly_type) as anomaly_types,
    MAX(a.severity) as max_severity,
    MAX(a.detected_at) as last_anomaly
FROM observed_files f
JOIN anomalies a ON f.file_id = a.file_id
WHERE NOT a.resolved
GROUP BY f.path
ORDER BY anomaly_count DESC;

-- GF(3) conservation check
CREATE OR REPLACE VIEW gf3_violations AS
SELECT 
    t.triplet_id,
    f.path,
    t.timestamp,
    t.trit_sum,
    t.gf3_conserved,
    t.size_consistent,
    t.inode_consistent
FROM observation_triplets t
JOIN observed_files f ON t.file_id = f.file_id
WHERE NOT t.gf3_conserved
   OR NOT t.size_consistent
   OR NOT t.inode_consistent;

-- Ghost file summary
CREATE OR REPLACE VIEW ghost_summary AS
SELECT 
    directory,
    ghost_type,
    COUNT(*) as count,
    LIST(file_path) as files
FROM ghost_files
WHERE NOT is_resolved
GROUP BY directory, ghost_type;

-- Observation method statistics
CREATE OR REPLACE VIEW method_stats AS
SELECT 
    method,
    trit,
    COUNT(*) as observation_count,
    AVG(elapsed_us) as avg_elapsed_us,
    COUNT(*) FILTER (WHERE error IS NOT NULL) as error_count
FROM observations
GROUP BY method, trit
ORDER BY trit, method;

-- ═══════════════════════════════════════════════════════════════════════════
-- INDEXES
-- ═══════════════════════════════════════════════════════════════════════════

CREATE INDEX IF NOT EXISTS idx_obs_file_time ON observations(file_id, timestamp);
CREATE INDEX IF NOT EXISTS idx_obs_method ON observations(method);
CREATE INDEX IF NOT EXISTS idx_anomaly_file ON anomalies(file_id);
CREATE INDEX IF NOT EXISTS idx_anomaly_type ON anomalies(anomaly_type);
CREATE INDEX IF NOT EXISTS idx_ghost_dir ON ghost_files(directory);
CREATE INDEX IF NOT EXISTS idx_flicker_file ON flickers(file_id);
