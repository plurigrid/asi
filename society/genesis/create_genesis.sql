-- World Genesis DuckLake Schema
-- Creates the complete knowledge transfer database for Aptos worlds system
-- NO PRIVATE KEYS - only public addresses and regeneration instructions

-- ============================================================
-- THREADS: Amp and Claude conversation history
-- ============================================================

CREATE TABLE IF NOT EXISTS amp_threads (
    thread_id VARCHAR PRIMARY KEY,
    title VARCHAR,
    created_at TIMESTAMP,
    updated_at TIMESTAMP,
    message_count INTEGER,
    matched_text TEXT,
    relevance_score FLOAT DEFAULT 1.0
);

CREATE TABLE IF NOT EXISTS claude_history (
    id INTEGER PRIMARY KEY,
    timestamp TIMESTAMP,
    role VARCHAR,  -- 'user' or 'assistant'
    content TEXT,
    tool_calls JSON,
    session_id VARCHAR
);

-- ============================================================
-- MOVE CONTRACTS: Source code for on-chain deployment
-- ============================================================

CREATE TABLE IF NOT EXISTS move_contracts (
    contract_id VARCHAR PRIMARY KEY,
    module_name VARCHAR,
    file_path VARCHAR,
    content TEXT,
    deployed_address VARCHAR,
    network VARCHAR DEFAULT 'mainnet',
    deploy_tx VARCHAR,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- ============================================================
-- SKILLS: All skills needed for the system
-- ============================================================

CREATE TABLE IF NOT EXISTS skills (
    skill_name VARCHAR PRIMARY KEY,
    file_path VARCHAR,
    description TEXT,
    trit INTEGER CHECK (trit IN (-1, 0, 1)),
    role VARCHAR,  -- 'MINUS', 'ERGODIC', 'PLUS'
    dependencies JSON,
    content TEXT
);

-- ============================================================
-- WALLETS: Public addresses only (NO PRIVATE KEYS)
-- ============================================================

CREATE TABLE IF NOT EXISTS wallets (
    wallet_name VARCHAR PRIMARY KEY,
    public_address VARCHAR,
    trit INTEGER CHECK (trit IN (-1, 0, 1)),
    role VARCHAR,
    network VARCHAR DEFAULT 'mainnet',
    created_at TIMESTAMP,
    balance_apt DECIMAL(20,8),
    mcp_server_name VARCHAR
);

-- ============================================================
-- MCP CONFIG: Templates for MCP server configuration
-- ============================================================

CREATE TABLE IF NOT EXISTS mcp_config_templates (
    server_name VARCHAR PRIMARY KEY,
    command VARCHAR,
    args_template JSON,
    env_template JSON,
    description TEXT
);

-- ============================================================
-- BOOTSTRAP PROMPTS: One-interaction regeneration prompts
-- ============================================================

CREATE TABLE IF NOT EXISTS bootstrap_prompts (
    prompt_name VARCHAR PRIMARY KEY,
    content TEXT,
    version VARCHAR,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- ============================================================
-- GF(3) MANIFEST: Conservation verification
-- ============================================================

CREATE TABLE IF NOT EXISTS gf3_manifest (
    entity_type VARCHAR,
    entity_name VARCHAR,
    trit INTEGER CHECK (trit IN (-1, 0, 1)),
    role VARCHAR,
    PRIMARY KEY (entity_type, entity_name)
);

CREATE TABLE IF NOT EXISTS gf3_triads (
    triad_id INTEGER PRIMARY KEY,
    entity_type VARCHAR,
    minus_entity VARCHAR,
    ergodic_entity VARCHAR,
    plus_entity VARCHAR,
    sum_verified BOOLEAN DEFAULT TRUE
);

-- ============================================================
-- WORLDNET LEDGER: Off-chain claim tracking
-- ============================================================

CREATE TABLE IF NOT EXISTS worldnet_events (
    event_id INTEGER PRIMARY KEY,
    epoch INTEGER,
    agent VARCHAR,
    role VARCHAR,
    action VARCHAR,
    delta_claims DECIMAL(20,8),
    reason TEXT,
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE IF NOT EXISTS worldnet_agents (
    agent_name VARCHAR PRIMARY KEY,
    wallet_address VARCHAR,
    current_claims DECIMAL(20,8) DEFAULT 0,
    total_minted DECIMAL(20,8) DEFAULT 0,
    total_decayed DECIMAL(20,8) DEFAULT 0
);

-- ============================================================
-- SCRIPTS: Babashka/Clojure scripts for regeneration
-- ============================================================

CREATE TABLE IF NOT EXISTS scripts (
    script_name VARCHAR PRIMARY KEY,
    file_path VARCHAR,
    content TEXT,
    language VARCHAR DEFAULT 'clojure',
    description TEXT
);

-- ============================================================
-- VIEWS: Useful aggregations
-- ============================================================

CREATE VIEW IF NOT EXISTS wallet_summary AS
SELECT 
    wallet_name,
    public_address,
    trit,
    role,
    balance_apt,
    mcp_server_name
FROM wallets
ORDER BY wallet_name;

CREATE VIEW IF NOT EXISTS gf3_verification AS
SELECT 
    entity_type,
    SUM(trit) as trit_sum,
    CASE WHEN SUM(trit) % 3 = 0 THEN 'CONSERVED' ELSE 'VIOLATION' END as status,
    COUNT(*) as entity_count
FROM gf3_manifest
GROUP BY entity_type;

CREATE VIEW IF NOT EXISTS skill_triads AS
SELECT 
    s1.skill_name as minus_skill,
    s2.skill_name as ergodic_skill,
    s3.skill_name as plus_skill,
    (s1.trit + s2.trit + s3.trit) as trit_sum
FROM skills s1
CROSS JOIN skills s2
CROSS JOIN skills s3
WHERE s1.trit = -1 AND s2.trit = 0 AND s3.trit = 1
  AND s1.skill_name < s2.skill_name
  AND s2.skill_name < s3.skill_name
LIMIT 100;
