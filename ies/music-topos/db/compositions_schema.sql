-- Compositions Schema for Skills Argue System
-- GF(3) conserved triads of musical compositions

CREATE TABLE IF NOT EXISTS compositions (
    id VARCHAR PRIMARY KEY,
    name VARCHAR NOT NULL,
    composer VARCHAR NOT NULL,
    form VARCHAR NOT NULL,  -- limit, colimit, list, name
    trit INTEGER NOT NULL CHECK (trit IN (-1, 0, 1)),
    domain VARCHAR NOT NULL,
    year INTEGER,
    duration_min INTEGER,
    created_at TIMESTAMP DEFAULT current_timestamp
);

CREATE TABLE IF NOT EXISTS composition_morphisms (
    id VARCHAR PRIMARY KEY,
    composition_id VARCHAR REFERENCES compositions(id),
    morphism_name VARCHAR NOT NULL,
    morphism_order INTEGER NOT NULL,
    created_at TIMESTAMP DEFAULT current_timestamp
);

CREATE TABLE IF NOT EXISTS composition_denotators (
    composition_id VARCHAR REFERENCES compositions(id),
    key VARCHAR NOT NULL,
    value VARCHAR NOT NULL,
    PRIMARY KEY (composition_id, key)
);

CREATE TABLE IF NOT EXISTS argumentation_rounds (
    id VARCHAR PRIMARY KEY,
    seed VARCHAR NOT NULL,
    round_number INTEGER NOT NULL,
    selected_composition_id VARCHAR REFERENCES compositions(id),
    selected_by_skill VARCHAR NOT NULL,
    walk_position VARCHAR,  -- JSON array [x, y]
    gf3_running_sum INTEGER,
    created_at TIMESTAMP DEFAULT current_timestamp
);

CREATE TABLE IF NOT EXISTS composition_broadcasts (
    id VARCHAR PRIMARY KEY,
    seed VARCHAR NOT NULL,
    epoch INTEGER NOT NULL,
    composition_id VARCHAR REFERENCES compositions(id),
    morphism VARCHAR NOT NULL,
    triplet_minus INTEGER,
    triplet_ergodic INTEGER,
    triplet_plus INTEGER,
    gf3_conserved BOOLEAN,
    created_at TIMESTAMP DEFAULT current_timestamp
);

-- View: GF(3) triads
CREATE OR REPLACE VIEW composition_triads AS
SELECT 
    seed,
    LIST(name ORDER BY round_number) as compositions,
    LIST(trit ORDER BY round_number) as trits,
    SUM(trit) as gf3_sum,
    SUM(trit) % 3 = 0 as gf3_conserved
FROM argumentation_rounds ar
JOIN compositions c ON ar.selected_composition_id = c.id
GROUP BY seed;

-- View: Morphism frequency
CREATE OR REPLACE VIEW morphism_frequency AS
SELECT 
    morphism_name,
    COUNT(*) as usage_count,
    LIST(DISTINCT c.composer) as composers
FROM composition_morphisms cm
JOIN compositions c ON cm.composition_id = c.id
GROUP BY morphism_name
ORDER BY usage_count DESC;

-- ═══════════════════════════════════════════════════════════════════════════
-- BITEMPORAL EXTENSION (CoW/CoR aware)
-- ═══════════════════════════════════════════════════════════════════════════
-- Transaction time: when recorded in DB (system-managed)
-- Valid time: when true in the real world (user-managed)

CREATE TABLE IF NOT EXISTS composition_history (
    id VARCHAR,
    name VARCHAR,
    composer VARCHAR,
    form VARCHAR,
    trit INTEGER,
    domain VARCHAR,
    -- Bitemporal columns
    valid_from TIMESTAMP NOT NULL,
    valid_to TIMESTAMP DEFAULT 'infinity',
    transaction_from TIMESTAMP DEFAULT current_timestamp,
    transaction_to TIMESTAMP DEFAULT 'infinity',
    -- CoW tracking
    cow_source_id VARCHAR,  -- If cloned, reference to source
    fs_birthtime TIMESTAMP,  -- APFS creation time
    fs_mtime TIMESTAMP,      -- APFS modification time
    PRIMARY KEY (id, valid_from, transaction_from)
);

-- View: Current valid state
CREATE OR REPLACE VIEW compositions_current AS
SELECT * FROM composition_history
WHERE current_timestamp BETWEEN valid_from AND valid_to
  AND current_timestamp BETWEEN transaction_from AND transaction_to;

-- View: As-of query (time travel)
CREATE OR REPLACE MACRO compositions_as_of(as_of_time) AS TABLE
SELECT * FROM composition_history
WHERE as_of_time BETWEEN valid_from AND valid_to
  AND as_of_time BETWEEN transaction_from AND transaction_to;
