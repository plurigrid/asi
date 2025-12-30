-- Worldnet Ledger Schema for Path A
-- Intelligence competes here; money settles once on-chain.
--
-- INVARIANT: sum(agent_claims) + unallocated_claims = total_claims

-- Append-only event log (source of truth)
CREATE TABLE IF NOT EXISTS events (
    event_id INTEGER PRIMARY KEY,
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    epoch INTEGER NOT NULL,
    agent TEXT NOT NULL,                    -- agent identifier
    role TEXT CHECK(role IN ('PLUS', 'ERGODIC', 'MINUS')),
    action TEXT NOT NULL,                   -- MINT, DECAY, TRANSFER, FREEZE
    delta_claims DECIMAL(20,8) NOT NULL,    -- positive = mint, negative = burn/decay
    reason TEXT,                            -- artifact hash, quest id, etc
    bifurcation_addr TEXT,                  -- on-chain reference if applicable
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Materialized agent balances (derived from events)
CREATE TABLE IF NOT EXISTS agent_claims (
    agent TEXT PRIMARY KEY,
    claims DECIMAL(20,8) NOT NULL DEFAULT 0,
    last_epoch INTEGER NOT NULL DEFAULT 0,
    role TEXT CHECK(role IN ('PLUS', 'ERGODIC', 'MINUS')),
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Global state
CREATE TABLE IF NOT EXISTS worldnet_state (
    id INTEGER PRIMARY KEY CHECK(id = 1),   -- singleton
    current_epoch INTEGER NOT NULL DEFAULT 0,
    total_claims DECIMAL(20,8) NOT NULL DEFAULT 0,
    unallocated_claims DECIMAL(20,8) NOT NULL DEFAULT 0,
    decay_rate_bps INTEGER NOT NULL DEFAULT 693,  -- 6.93% per epoch
    epoch_duration_seconds INTEGER NOT NULL DEFAULT 3600,
    last_epoch_time TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Initialize singleton
INSERT OR IGNORE INTO worldnet_state (id, current_epoch, total_claims, unallocated_claims)
VALUES (1, 0, 0, 0);

-- Bifurcation tracking (mirrors on-chain state for reference)
CREATE TABLE IF NOT EXISTS bifurcations (
    bifurcation_addr TEXT PRIMARY KEY,
    belief_a TEXT NOT NULL,
    belief_b TEXT NOT NULL,
    apt_locked DECIMAL(20,8) NOT NULL,
    created_epoch INTEGER NOT NULL,
    resolved BOOLEAN DEFAULT FALSE,
    winner TEXT,  -- 'A' or 'B'
    resolved_epoch INTEGER,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Artifact registry (what agents produce)
CREATE TABLE IF NOT EXISTS artifacts (
    artifact_id TEXT PRIMARY KEY,           -- content hash
    creator_agent TEXT NOT NULL,
    artifact_type TEXT NOT NULL,            -- HYPOTHESIS, PROOF, REPRODUCTION, CANON
    parent_artifact TEXT,                   -- for derivations
    claims_minted DECIMAL(20,8) NOT NULL DEFAULT 0,
    verified_by TEXT,                       -- MINUS agent who verified
    frozen_by TEXT,                         -- ERGODIC agent who canonicalized
    created_epoch INTEGER NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Views for leaderboard

CREATE VIEW IF NOT EXISTS leaderboard AS
SELECT
    agent,
    claims,
    role,
    ROUND(100.0 * claims / NULLIF((SELECT total_claims FROM worldnet_state WHERE id = 1), 0), 2) as pct_share,
    updated_at
FROM agent_claims
ORDER BY claims DESC;

CREATE VIEW IF NOT EXISTS epoch_summary AS
SELECT
    epoch,
    SUM(CASE WHEN delta_claims > 0 THEN delta_claims ELSE 0 END) as minted,
    SUM(CASE WHEN delta_claims < 0 THEN ABS(delta_claims) ELSE 0 END) as decayed,
    COUNT(DISTINCT agent) as active_agents
FROM events
GROUP BY epoch
ORDER BY epoch DESC;
