-- Event Indexer Schema for GayMove Contract Events
-- Watches Aptos mainnet for PartitionEvent, MergeEvent, SettleEvent
-- Feeds into worldnet ledger with temporal versioning (SCD Type 2)
--
-- INVARIANT: All events have valid_from/valid_to for time-travel queries
-- INVARIANT: Indexer state tracks last_processed_version for resumable polling

-- ============================================================
-- PARTITION EVENTS (Belief creation/branching)
-- ============================================================
CREATE TABLE IF NOT EXISTS partition_events (
    id INTEGER PRIMARY KEY,
    partition_id TEXT NOT NULL,           -- On-chain partition identifier
    account TEXT NOT NULL,                -- Creator account address
    verse_in TEXT NOT NULL,               -- Source verse/belief state
    verse_out TEXT NOT NULL,              -- Target verse/belief state
    apt_amount DECIMAL(20,8),             -- APT locked in partition
    tx_hash TEXT NOT NULL UNIQUE,         -- Transaction hash
    tx_version BIGINT NOT NULL,           -- Aptos transaction version
    event_sequence BIGINT NOT NULL,       -- Event sequence number
    block_height BIGINT,                  -- Block height
    timestamp TIMESTAMP NOT NULL,         -- Event timestamp (from chain)
    
    -- Temporal versioning (SCD Type 2)
    valid_from TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    valid_to TIMESTAMP DEFAULT '9999-12-31 23:59:59',
    is_current BOOLEAN DEFAULT TRUE,
    
    -- GF(3) trit assignment (derived from partition_id hash)
    trit INTEGER CHECK(trit IN (-1, 0, 1)),
    
    -- Indexer metadata
    indexed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    index_version INTEGER DEFAULT 1
);

CREATE INDEX IF NOT EXISTS idx_partition_account ON partition_events(account);
CREATE INDEX IF NOT EXISTS idx_partition_timestamp ON partition_events(timestamp);
CREATE INDEX IF NOT EXISTS idx_partition_version ON partition_events(tx_version);
CREATE INDEX IF NOT EXISTS idx_partition_valid ON partition_events(valid_from, valid_to);

-- ============================================================
-- MERGE EVENTS (Belief convergence)
-- ============================================================
CREATE TABLE IF NOT EXISTS merge_events (
    id INTEGER PRIMARY KEY,
    partition_id_a TEXT NOT NULL,         -- First partition being merged
    partition_id_b TEXT NOT NULL,         -- Second partition being merged
    merged_id TEXT NOT NULL,              -- Resulting merged partition
    account TEXT NOT NULL,                -- Account that triggered merge
    tx_hash TEXT NOT NULL UNIQUE,
    tx_version BIGINT NOT NULL,
    event_sequence BIGINT NOT NULL,
    block_height BIGINT,
    timestamp TIMESTAMP NOT NULL,
    
    -- Temporal versioning (SCD Type 2)
    valid_from TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    valid_to TIMESTAMP DEFAULT '9999-12-31 23:59:59',
    is_current BOOLEAN DEFAULT TRUE,
    
    -- GF(3) conservation check: trit_a + trit_b should balance
    trit_a INTEGER CHECK(trit_a IN (-1, 0, 1)),
    trit_b INTEGER CHECK(trit_b IN (-1, 0, 1)),
    merged_trit INTEGER CHECK(merged_trit IN (-1, 0, 1)),
    
    indexed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    index_version INTEGER DEFAULT 1
);

CREATE INDEX IF NOT EXISTS idx_merge_timestamp ON merge_events(timestamp);
CREATE INDEX IF NOT EXISTS idx_merge_version ON merge_events(tx_version);
CREATE INDEX IF NOT EXISTS idx_merge_partitions ON merge_events(partition_id_a, partition_id_b);

-- ============================================================
-- SETTLE EVENTS (Belief resolution/payout)
-- ============================================================
CREATE TABLE IF NOT EXISTS settle_events (
    id INTEGER PRIMARY KEY,
    partition_id TEXT NOT NULL,           -- Settled partition
    account TEXT NOT NULL,                -- Account receiving payout
    final_belief TEXT NOT NULL,           -- Winning belief state
    payout DECIMAL(20,8) NOT NULL,        -- APT payout amount
    original_stake DECIMAL(20,8),         -- Original stake for reference
    profit_loss DECIMAL(20,8),            -- Net P&L
    tx_hash TEXT NOT NULL UNIQUE,
    tx_version BIGINT NOT NULL,
    event_sequence BIGINT NOT NULL,
    block_height BIGINT,
    timestamp TIMESTAMP NOT NULL,
    
    -- Temporal versioning (SCD Type 2)
    valid_from TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    valid_to TIMESTAMP DEFAULT '9999-12-31 23:59:59',
    is_current BOOLEAN DEFAULT TRUE,
    
    -- Settlement metadata
    trit INTEGER CHECK(trit IN (-1, 0, 1)),
    settlement_type TEXT CHECK(settlement_type IN ('CORRECT', 'INCORRECT', 'PARTIAL')),
    
    indexed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    index_version INTEGER DEFAULT 1
);

CREATE INDEX IF NOT EXISTS idx_settle_account ON settle_events(account);
CREATE INDEX IF NOT EXISTS idx_settle_timestamp ON settle_events(timestamp);
CREATE INDEX IF NOT EXISTS idx_settle_version ON settle_events(tx_version);

-- ============================================================
-- INDEXER STATE (Checkpoint tracking)
-- ============================================================
CREATE TABLE IF NOT EXISTS indexer_state (
    id INTEGER PRIMARY KEY CHECK(id = 1),  -- Singleton
    last_processed_version BIGINT NOT NULL DEFAULT 0,
    last_processed_timestamp TIMESTAMP,
    checkpoint_time TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    
    -- Contract address being indexed
    contract_address TEXT NOT NULL,
    module_name TEXT DEFAULT 'gaymove',
    
    -- Indexer health
    events_processed_total BIGINT DEFAULT 0,
    last_error TEXT,
    last_error_time TIMESTAMP,
    consecutive_errors INTEGER DEFAULT 0,
    
    -- Polling config
    poll_interval_ms INTEGER DEFAULT 1000,
    batch_size INTEGER DEFAULT 100,
    
    -- Temporal checkpoint for replay
    replay_from_version BIGINT,           -- Set to replay from specific version
    replay_requested_at TIMESTAMP,
    
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Initialize singleton with GayMove contract address
INSERT OR IGNORE INTO indexer_state (
    id, 
    contract_address, 
    last_processed_version
) VALUES (
    1, 
    '0x8699edc0960dd5b916074f1e9bd25d86fb416a8decfa46f78ab0af6eaebe9d7a',
    0
);

-- ============================================================
-- REPLAY HISTORY (For temporal debugging)
-- ============================================================
CREATE TABLE IF NOT EXISTS replay_history (
    id INTEGER PRIMARY KEY,
    replay_from_version BIGINT NOT NULL,
    replay_to_version BIGINT NOT NULL,
    events_replayed INTEGER NOT NULL,
    started_at TIMESTAMP NOT NULL,
    completed_at TIMESTAMP,
    status TEXT CHECK(status IN ('RUNNING', 'COMPLETED', 'FAILED', 'CANCELLED')),
    error_message TEXT
);

-- ============================================================
-- VIEWS FOR WORLDNET INTEGRATION
-- ============================================================

-- Current partition states (active partitions)
CREATE VIEW IF NOT EXISTS active_partitions AS
SELECT 
    partition_id,
    account,
    verse_in,
    verse_out,
    apt_amount,
    trit,
    timestamp as created_at,
    tx_hash
FROM partition_events
WHERE is_current = TRUE
  AND partition_id NOT IN (
    SELECT partition_id FROM settle_events WHERE is_current = TRUE
  )
  AND partition_id NOT IN (
    SELECT partition_id_a FROM merge_events WHERE is_current = TRUE
  )
  AND partition_id NOT IN (
    SELECT partition_id_b FROM merge_events WHERE is_current = TRUE
  );

-- Settlement history with P&L
CREATE VIEW IF NOT EXISTS settlement_summary AS
SELECT 
    account,
    COUNT(*) as total_settlements,
    SUM(payout) as total_payout,
    SUM(original_stake) as total_staked,
    SUM(profit_loss) as net_pnl,
    AVG(profit_loss) as avg_pnl,
    SUM(CASE WHEN settlement_type = 'CORRECT' THEN 1 ELSE 0 END) as correct_predictions,
    SUM(CASE WHEN settlement_type = 'INCORRECT' THEN 1 ELSE 0 END) as incorrect_predictions
FROM settle_events
WHERE is_current = TRUE
GROUP BY account;

-- GF(3) trit distribution across events
CREATE VIEW IF NOT EXISTS trit_distribution AS
SELECT 
    'partition' as event_type,
    trit,
    COUNT(*) as count
FROM partition_events WHERE is_current = TRUE
GROUP BY trit
UNION ALL
SELECT 
    'merge_a' as event_type,
    trit_a as trit,
    COUNT(*) as count
FROM merge_events WHERE is_current = TRUE
GROUP BY trit_a
UNION ALL
SELECT 
    'settle' as event_type,
    trit,
    COUNT(*) as count
FROM settle_events WHERE is_current = TRUE
GROUP BY trit;

-- Time-travel query helper: state at given timestamp
CREATE VIEW IF NOT EXISTS partition_state_template AS
SELECT 
    partition_id,
    account,
    verse_in,
    verse_out,
    apt_amount,
    trit,
    valid_from,
    valid_to
FROM partition_events;
-- Usage: SELECT * FROM partition_state_template WHERE valid_from <= ?target_time AND valid_to > ?target_time

-- Join indexed events with worldnet claims (for agent-bridge integration)
CREATE VIEW IF NOT EXISTS event_claims_join AS
SELECT 
    p.partition_id,
    p.account,
    p.verse_out as belief,
    p.apt_amount,
    p.trit,
    CASE 
        WHEN p.trit = 1 THEN 'PLUS'
        WHEN p.trit = 0 THEN 'ERGODIC'
        WHEN p.trit = -1 THEN 'MINUS'
    END as role,
    s.payout,
    s.settlement_type,
    p.timestamp as partition_time,
    s.timestamp as settle_time
FROM partition_events p
LEFT JOIN settle_events s 
    ON p.partition_id = s.partition_id 
    AND s.is_current = TRUE
WHERE p.is_current = TRUE;

-- ============================================================
-- TEMPORAL FUNCTIONS (Time-travel queries)
-- ============================================================

-- Get partition state at specific timestamp
-- Usage: SELECT * FROM partition_at_time('2024-01-15 12:00:00');
-- Note: DuckDB syntax - implement as prepared statement in indexer
