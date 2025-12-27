-- Thread Operad Materialization Schema
-- DiscoHy + ACSets integration
-- 
-- This schema materializes the thread tree as a rooted color operad
-- with dynamically selectable operad variants (dendroidal, colored-symmetric,
-- actegory, 2-transducer).
--
-- GF(3) Conservation: sum(trits) ≡ 0 (mod 3) for each triplet of siblings

-- ═══════════════════════════════════════════════════════════════════════════════
-- CORE TABLES
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE TABLE IF NOT EXISTS thread_nodes (
    thread_id VARCHAR PRIMARY KEY,
    title VARCHAR,
    seed UBIGINT,
    parent_id VARCHAR REFERENCES thread_nodes(thread_id),
    arity INTEGER DEFAULT 0,
    trit INTEGER CHECK (trit IN (-1, 0, 1)),
    message_count INTEGER DEFAULT 0,
    created_at TIMESTAMP,
    updated_at TIMESTAMP,
    
    -- 3 parallel color streams (LCH color space)
    -- LIVE (+1): Forward, real-time
    live_l DOUBLE,  -- Lightness 0-100
    live_c DOUBLE,  -- Chroma 0-150
    live_h DOUBLE,  -- Hue 0-360
    
    -- VERIFY (0): Verification, neutral
    verify_l DOUBLE,
    verify_c DOUBLE,
    verify_h DOUBLE,
    
    -- BACKFILL (-1): Historical, archived
    backfill_l DOUBLE,
    backfill_c DOUBLE,
    backfill_h DOUBLE,
    
    -- Operad metadata
    depth INTEGER DEFAULT 0,  -- Distance from root
    subtree_size INTEGER DEFAULT 1  -- Number of descendants + self
);

-- ═══════════════════════════════════════════════════════════════════════════════
-- OPERAD COMPOSITION TRACKING
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE TABLE IF NOT EXISTS operad_compositions (
    composition_id VARCHAR PRIMARY KEY,
    outer_thread_id VARCHAR REFERENCES thread_nodes(thread_id),
    inner_thread_id VARCHAR REFERENCES thread_nodes(thread_id),
    port INTEGER,
    variant VARCHAR,
    result_arity INTEGER,
    result_json JSON,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- ═══════════════════════════════════════════════════════════════════════════════
-- OPERAD VARIANTS: Dynamically Selectable
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE TABLE IF NOT EXISTS operad_variants (
    name VARCHAR PRIMARY KEY,
    description VARCHAR,
    composition_rule VARCHAR,  -- JSON describing composition semantics
    is_active BOOLEAN DEFAULT FALSE,
    trit INTEGER CHECK (trit IN (-1, 0, 1))  -- Variant's own trit
);

-- Insert default variants with trit assignments
INSERT OR REPLACE INTO operad_variants VALUES
    ('dendroidal', 
     'Tree-structured operations with edge coloring. Ω(T) construction from mathpix snip 9fda228d.',
     '{"type": "graft", "rule": "substitute at leaf"}',
     TRUE, 0),
    ('colored-symmetric', 
     'Symmetric group action on colors. Left Kan extension to Σ-colored from snip 0c9f8554.',
     '{"type": "symmetric", "rule": "permutation tracking"}',
     FALSE, -1),
    ('actegory', 
     'Monoidal category M acting on category C. Parametrised morphisms from snip 12a80732.',
     '{"type": "action", "rule": "monoidal parameter"}',
     FALSE, 0),
    ('2-transducer', 
     'Loregian categorical automata. (Q,t): A•→B with state from paper_extracts.',
     '{"type": "transducer", "rule": "Day convolution on state"}',
     FALSE, 1);

-- ═══════════════════════════════════════════════════════════════════════════════
-- COLOR STREAM HISTORY (DiscoHy Time Travel)
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE TABLE IF NOT EXISTS color_stream_history (
    id INTEGER PRIMARY KEY,
    thread_id VARCHAR REFERENCES thread_nodes(thread_id),
    stream VARCHAR CHECK (stream IN ('LIVE', 'VERIFY', 'BACKFILL')),
    index_position INTEGER,
    l DOUBLE,
    c DOUBLE,
    h DOUBLE,
    trit INTEGER,
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- ═══════════════════════════════════════════════════════════════════════════════
-- VIEWS: GF(3) Conservation Analysis
-- ═══════════════════════════════════════════════════════════════════════════════

-- Check GF(3) conservation for sibling triplets
CREATE OR REPLACE VIEW gf3_sibling_triplets AS
WITH numbered_siblings AS (
    SELECT 
        thread_id,
        parent_id,
        trit,
        created_at,
        ROW_NUMBER() OVER (PARTITION BY parent_id ORDER BY created_at) as sibling_order
    FROM thread_nodes
    WHERE parent_id IS NOT NULL
),
triplets AS (
    SELECT 
        a.parent_id,
        a.thread_id as t1, a.trit as trit1,
        b.thread_id as t2, b.trit as trit2,
        c.thread_id as t3, c.trit as trit3,
        (a.trit + b.trit + c.trit) as trit_sum,
        MOD(a.trit + b.trit + c.trit, 3) as gf3_residue
    FROM numbered_siblings a
    JOIN numbered_siblings b ON a.parent_id = b.parent_id 
        AND b.sibling_order = a.sibling_order + 1
    JOIN numbered_siblings c ON a.parent_id = c.parent_id 
        AND c.sibling_order = a.sibling_order + 2
)
SELECT 
    parent_id,
    t1, trit1, t2, trit2, t3, trit3,
    trit_sum,
    gf3_residue,
    CASE WHEN gf3_residue = 0 THEN 'CONSERVED' ELSE 'VIOLATION' END as status
FROM triplets;

-- Summary of GF(3) conservation
CREATE OR REPLACE VIEW gf3_conservation_summary AS
SELECT 
    COUNT(*) as total_triplets,
    SUM(CASE WHEN gf3_residue = 0 THEN 1 ELSE 0 END) as conserved,
    SUM(CASE WHEN gf3_residue != 0 THEN 1 ELSE 0 END) as violations,
    ROUND(100.0 * SUM(CASE WHEN gf3_residue = 0 THEN 1 ELSE 0 END) / COUNT(*), 2) as conservation_pct
FROM gf3_sibling_triplets;

-- ═══════════════════════════════════════════════════════════════════════════════
-- VIEWS: Operad Structure Analysis
-- ═══════════════════════════════════════════════════════════════════════════════

-- Tree structure with depth and path
CREATE OR REPLACE VIEW thread_tree AS
WITH RECURSIVE tree AS (
    -- Base: roots (no parent)
    SELECT 
        thread_id, title, parent_id, trit,
        0 as depth,
        thread_id as path,
        1 as subtree_size
    FROM thread_nodes
    WHERE parent_id IS NULL
    
    UNION ALL
    
    -- Recursive: children
    SELECT 
        n.thread_id, n.title, n.parent_id, n.trit,
        t.depth + 1,
        t.path || ' → ' || n.thread_id,
        1
    FROM thread_nodes n
    JOIN tree t ON n.parent_id = t.thread_id
)
SELECT * FROM tree;

-- Operad arity distribution
CREATE OR REPLACE VIEW operad_arity_distribution AS
SELECT 
    arity,
    COUNT(*) as count,
    ROUND(100.0 * COUNT(*) / SUM(COUNT(*)) OVER (), 2) as pct
FROM thread_nodes
GROUP BY arity
ORDER BY arity;

-- Trit distribution by depth
CREATE OR REPLACE VIEW trit_by_depth AS
SELECT 
    depth,
    SUM(CASE WHEN trit = 1 THEN 1 ELSE 0 END) as plus_count,
    SUM(CASE WHEN trit = 0 THEN 1 ELSE 0 END) as ergodic_count,
    SUM(CASE WHEN trit = -1 THEN 1 ELSE 0 END) as minus_count,
    SUM(trit) as trit_sum,
    MOD(SUM(trit), 3) as gf3_residue
FROM thread_tree
GROUP BY depth
ORDER BY depth;

-- ═══════════════════════════════════════════════════════════════════════════════
-- VIEWS: DisCoPy / Monoidal Diagram Structure
-- ═══════════════════════════════════════════════════════════════════════════════

-- Boxes (threads as morphisms)
CREATE OR REPLACE VIEW discopy_boxes AS
SELECT 
    thread_id as box_id,
    title as box_name,
    COALESCE(parent_id, 'ROOT') as domain,
    arity as codomain_count,
    live_h as color_hue,
    trit as color_trit,
    CASE trit 
        WHEN 1 THEN '#D82626'
        WHEN 0 THEN '#26D826'
        WHEN -1 THEN '#2626D8'
    END as color_hex
FROM thread_nodes;

-- Wires (edges between threads)
CREATE OR REPLACE VIEW discopy_wires AS
SELECT 
    p.thread_id as source,
    c.thread_id as target,
    c.trit as wire_trit,
    c.verify_h as wire_hue,
    CASE c.trit 
        WHEN 1 THEN 'LIVE'
        WHEN 0 THEN 'VERIFY'
        WHEN -1 THEN 'BACKFILL'
    END as wire_label
FROM thread_nodes p
JOIN thread_nodes c ON c.parent_id = p.thread_id;

-- ═══════════════════════════════════════════════════════════════════════════════
-- FUNCTIONS: Color Generation (SplitMix64)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Note: DuckDB doesn't have UDFs in pure SQL, but we can use macros
CREATE OR REPLACE MACRO mix64(z) AS (
    -- Simplified SplitMix64 mix (approximation for SQL)
    (z * 0xbf58476d1ce4e5b9) % 18446744073709551615
);

CREATE OR REPLACE MACRO seed_to_hue(seed, idx) AS (
    -- Generate hue from seed at index
    MOD(mix64(seed + idx * 0x9e3779b97f4a7c15) / 18446744073709551615.0 * 360.0, 360.0)
);

CREATE OR REPLACE MACRO hue_to_trit(h) AS (
    -- Map hue to GF(3) trit
    CASE 
        WHEN h < 60 OR h >= 300 THEN 1   -- warm → PLUS
        WHEN h < 180 THEN 0              -- neutral → ERGODIC
        ELSE -1                          -- cool → MINUS
    END
);

-- ═══════════════════════════════════════════════════════════════════════════════
-- INDEXES
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE INDEX IF NOT EXISTS idx_thread_parent ON thread_nodes(parent_id);
CREATE INDEX IF NOT EXISTS idx_thread_trit ON thread_nodes(trit);
CREATE INDEX IF NOT EXISTS idx_thread_created ON thread_nodes(created_at);
CREATE INDEX IF NOT EXISTS idx_color_history_thread ON color_stream_history(thread_id, stream);

-- ═══════════════════════════════════════════════════════════════════════════════
-- SAMPLE DATA INSERTION (for testing)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Example: Insert a thread with all color streams
-- INSERT INTO thread_nodes (
--     thread_id, title, seed, parent_id, arity, trit, message_count, created_at,
--     live_l, live_c, live_h,
--     verify_l, verify_c, verify_h,
--     backfill_l, backfill_c, backfill_h,
--     depth, subtree_size
-- ) VALUES (
--     'T-019b438f-c843-7779-8812-bc0d6fe8b803',
--     'Synergistic skill triads and subagent coloring',
--     12345678901234567890,
--     NULL,
--     2,
--     1,
--     177,
--     '2025-12-21 01:30:55',
--     50.0, 80.0, 340.0,  -- LIVE: warm red
--     55.0, 60.0, 120.0,  -- VERIFY: green
--     45.0, 70.0, 240.0,  -- BACKFILL: blue
--     0,
--     3
-- );
