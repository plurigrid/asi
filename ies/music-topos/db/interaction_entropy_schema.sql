-- Interaction Entropy Schema
-- Every interaction includes deterministic entropy via SplitMixTernary
--
-- Architecture:
--   DiscoHy (Python/Hy) ←──→ DuckDB ←──→ ACSets.jl (Julia)
--
-- Key Invariants:
--   1. Every skill invocation derives seed from interaction hash
--   2. GF(3) conservation: sum(trits) ≡ 0 (mod 3) per triplet
--   3. Self-avoiding walk: colors form unique path
--   4. Spectral gap verification at probability 1/4
--
-- The schema models this as an ACSet (attributed C-set):
--   Objects: Interactions, Colors, Skills, Trits
--   Morphisms: interaction→color, interaction→skill, color→trit

-- ═══════════════════════════════════════════════════════════════════════════════
-- CORE TABLES: Interaction Entropy Capture
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE TABLE IF NOT EXISTS interactions (
    interaction_id VARCHAR PRIMARY KEY,
    thread_id VARCHAR,
    epoch INTEGER NOT NULL,
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    
    -- Entropy source: SHA256 of interaction content → seed
    entropy_hash VARCHAR NOT NULL,
    derived_seed UBIGINT NOT NULL,
    
    -- Position in self-avoiding walk
    walk_x INTEGER NOT NULL,
    walk_y INTEGER NOT NULL,
    walk_color_index INTEGER NOT NULL,
    
    -- Deterministic color (LCH from SplitMix64)
    color_l DOUBLE NOT NULL,
    color_c DOUBLE NOT NULL,
    color_h DOUBLE NOT NULL,
    
    -- GF(3) trit from hue
    trit INTEGER NOT NULL CHECK (trit IN (-1, 0, 1)),
    
    -- Verification state (spectral gap at 1/4)
    verified BOOLEAN DEFAULT FALSE,
    verification_epoch INTEGER,
    
    -- Skill context
    skill_name VARCHAR,
    skill_role VARCHAR CHECK (skill_role IN ('generator', 'coordinator', 'validator'))
);

CREATE TABLE IF NOT EXISTS interaction_triplets (
    triplet_id VARCHAR PRIMARY KEY,
    interaction_1_id VARCHAR REFERENCES interactions(interaction_id),
    interaction_2_id VARCHAR REFERENCES interactions(interaction_id),
    interaction_3_id VARCHAR REFERENCES interactions(interaction_id),
    
    -- Trits from each interaction
    trit_1 INTEGER,
    trit_2 INTEGER,
    trit_3 INTEGER,
    
    -- GF(3) check
    trit_sum INTEGER GENERATED ALWAYS AS (trit_1 + trit_2 + trit_3) VIRTUAL,
    gf3_residue INTEGER GENERATED ALWAYS AS (MOD(trit_1 + trit_2 + trit_3 + 300, 3)) VIRTUAL,
    gf3_conserved BOOLEAN GENERATED ALWAYS AS (MOD(trit_1 + trit_2 + trit_3 + 300, 3) = 0) VIRTUAL,
    
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- ═══════════════════════════════════════════════════════════════════════════════
-- SKILL INVOCATION TRACKING
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE TABLE IF NOT EXISTS skill_invocations (
    invocation_id VARCHAR PRIMARY KEY,
    interaction_id VARCHAR REFERENCES interactions(interaction_id),
    skill_name VARCHAR NOT NULL,
    skill_role VARCHAR CHECK (skill_role IN ('generator', 'coordinator', 'validator')),
    skill_trit INTEGER CHECK (skill_trit IN (-1, 0, 1)),
    
    -- Input/output types (from skill's world action)
    input_type VARCHAR,
    output_type VARCHAR,
    
    -- Entropy used for this invocation
    invocation_seed UBIGINT NOT NULL,
    
    -- Results
    result_json JSON,
    
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- ═══════════════════════════════════════════════════════════════════════════════
-- DISCOPY DIAGRAM REPRESENTATION
-- ═══════════════════════════════════════════════════════════════════════════════
-- Models interactions as boxes in a monoidal diagram

CREATE TABLE IF NOT EXISTS discopy_boxes (
    box_id VARCHAR PRIMARY KEY,
    interaction_id VARCHAR REFERENCES interactions(interaction_id),
    box_name VARCHAR NOT NULL,
    
    -- Domain/Codomain types
    domain_types JSON,  -- Array of type names
    codomain_types JSON,
    
    -- Color from interaction
    color_l DOUBLE,
    color_c DOUBLE,
    color_h DOUBLE,
    trit INTEGER,
    
    -- Position in diagram
    layer INTEGER,
    position_in_layer INTEGER
);

CREATE TABLE IF NOT EXISTS discopy_wires (
    wire_id VARCHAR PRIMARY KEY,
    source_box_id VARCHAR REFERENCES discopy_boxes(box_id),
    target_box_id VARCHAR REFERENCES discopy_boxes(box_id),
    wire_type VARCHAR NOT NULL,
    
    -- Wire carries trit from source
    trit INTEGER,
    
    -- TAP state: LIVE (+1), VERIFY (0), BACKFILL (-1)
    tap_state VARCHAR CHECK (tap_state IN ('LIVE', 'VERIFY', 'BACKFILL'))
);

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACSET EXPORT: C-Set Functor Representation
-- ═══════════════════════════════════════════════════════════════════════════════
-- Schema for exporting to Julia ACSets.jl

CREATE TABLE IF NOT EXISTS acset_objects (
    object_id INTEGER PRIMARY KEY,
    object_type VARCHAR NOT NULL,  -- 'Interaction', 'Color', 'Skill', 'Triplet'
    source_id VARCHAR NOT NULL,    -- FK to source table
    
    -- Cached attributes for fast export
    attributes JSON
);

CREATE TABLE IF NOT EXISTS acset_morphisms (
    morphism_id INTEGER PRIMARY KEY,
    morphism_name VARCHAR NOT NULL,  -- e.g., 'interaction_to_color', 'skill_to_interaction'
    source_object_id INTEGER REFERENCES acset_objects(object_id),
    target_object_id INTEGER REFERENCES acset_objects(object_id)
);

-- ═══════════════════════════════════════════════════════════════════════════════
-- VIEWS: Interaction Entropy Analysis
-- ═══════════════════════════════════════════════════════════════════════════════

-- GF(3) conservation status per epoch window
CREATE OR REPLACE VIEW gf3_epoch_conservation AS
WITH epoch_trits AS (
    SELECT 
        epoch / 3 as epoch_group,
        LIST(trit ORDER BY epoch) as trits,
        SUM(trit) as trit_sum,
        COUNT(*) as count
    FROM interactions
    GROUP BY epoch / 3
    HAVING COUNT(*) >= 3
)
SELECT 
    epoch_group,
    trits,
    trit_sum,
    MOD(trit_sum + 300, 3) as gf3_residue,
    MOD(trit_sum + 300, 3) = 0 as gf3_conserved
FROM epoch_trits;

-- Self-avoiding walk path
CREATE OR REPLACE VIEW walk_path AS
SELECT 
    epoch,
    walk_x,
    walk_y,
    walk_color_index,
    color_h,
    trit,
    LAG(walk_x) OVER (ORDER BY epoch) as prev_x,
    LAG(walk_y) OVER (ORDER BY epoch) as prev_y,
    (walk_x = LAG(walk_x) OVER (ORDER BY epoch) 
     AND walk_y = LAG(walk_y) OVER (ORDER BY epoch)) as is_revisit
FROM interactions
ORDER BY epoch;

-- Skill invocation by role
CREATE OR REPLACE VIEW skill_role_stats AS
SELECT 
    skill_role,
    COUNT(*) as invocation_count,
    AVG(skill_trit) as avg_trit,
    SUM(skill_trit) as total_trit_contribution,
    MOD(SUM(skill_trit) + 300, 3) as gf3_residue
FROM skill_invocations
GROUP BY skill_role;

-- DisCoPy diagram structure
CREATE OR REPLACE VIEW discopy_diagram_structure AS
SELECT 
    b.layer,
    b.position_in_layer,
    b.box_name,
    b.trit,
    STRING_AGG(w.wire_type, ', ') as incoming_wires,
    b.color_h as hue
FROM discopy_boxes b
LEFT JOIN discopy_wires w ON w.target_box_id = b.box_id
GROUP BY b.layer, b.position_in_layer, b.box_name, b.trit, b.color_h
ORDER BY b.layer, b.position_in_layer;

-- ═══════════════════════════════════════════════════════════════════════════════
-- MACROS: Entropy Generation (SplitMix64)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Note: Macros use decimal constants (DuckDB doesn't support hex in macros)
-- GOLDEN = 0x9E3779B97F4A7C15 = 11400714819323198485
-- MIX1 = 0xBF58476D1CE4E5B9 = 13787848793156543929

CREATE OR REPLACE MACRO splitmix64_next(state) AS (
    -- SplitMix64 mixing (simplified for SQL)
    ((state + 11400714819323198485) * 13787848793156543929) % 18446744073709551615
);

CREATE OR REPLACE MACRO derive_seed_from_hash(hash_str) AS (
    -- Convert first 16 hex chars to integer seed
    -- Note: DuckDB doesn't have hex string parsing, use application layer
    LENGTH(hash_str)  -- Placeholder - actual conversion done in Ruby/Julia/Hy
);

CREATE OR REPLACE MACRO hue_to_trit(h) AS (
    CASE 
        WHEN h < 60 OR h >= 300 THEN 1   -- warm → PLUS (+1)
        WHEN h < 180 THEN 0              -- neutral → ERGODIC (0)
        ELSE -1                          -- cool → MINUS (-1)
    END
);

CREATE OR REPLACE MACRO trit_to_role(t) AS (
    CASE t
        WHEN 1 THEN 'generator'
        WHEN 0 THEN 'coordinator'
        WHEN -1 THEN 'validator'
    END
);

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROCEDURES: Interaction Entropy Insertion
-- ═══════════════════════════════════════════════════════════════════════════════

-- Note: DuckDB doesn't have stored procedures, but we can create prepared statements
-- These would be called from Ruby/Julia/Hy code

-- Example: Insert interaction with full entropy derivation
-- PREPARE insert_interaction AS
-- INSERT INTO interactions (
--     interaction_id, thread_id, epoch, entropy_hash, derived_seed,
--     walk_x, walk_y, walk_color_index,
--     color_l, color_c, color_h, trit,
--     skill_name, skill_role
-- ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?);

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACSET EXPORT QUERIES (for Julia interop)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Export interactions as ACSet parts
CREATE OR REPLACE VIEW acset_interaction_parts AS
SELECT 
    ROW_NUMBER() OVER (ORDER BY epoch) as part_id,
    interaction_id,
    derived_seed,
    walk_x, walk_y,
    color_l, color_c, color_h,
    trit,
    skill_name
FROM interactions;

-- Export colors as ACSet parts  
CREATE OR REPLACE VIEW acset_color_parts AS
SELECT DISTINCT ON (color_l, color_c, color_h)
    ROW_NUMBER() OVER () as part_id,
    color_l as L,
    color_c as C,
    color_h as H,
    hue_to_trit(color_h) as trit
FROM interactions;

-- Export interaction→color morphism
CREATE OR REPLACE VIEW acset_interaction_to_color AS
SELECT 
    i.interaction_id,
    c.part_id as color_part_id
FROM interactions i
JOIN acset_color_parts c ON 
    i.color_l = c.L AND i.color_c = c.C AND i.color_h = c.H;

-- ═══════════════════════════════════════════════════════════════════════════════
-- INDEXES
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE INDEX IF NOT EXISTS idx_interaction_epoch ON interactions(epoch);
CREATE INDEX IF NOT EXISTS idx_interaction_thread ON interactions(thread_id);
CREATE INDEX IF NOT EXISTS idx_interaction_trit ON interactions(trit);
CREATE INDEX IF NOT EXISTS idx_interaction_walk ON interactions(walk_x, walk_y);
CREATE INDEX IF NOT EXISTS idx_skill_invocation_skill ON skill_invocations(skill_name);
CREATE INDEX IF NOT EXISTS idx_discopy_box_layer ON discopy_boxes(layer);
