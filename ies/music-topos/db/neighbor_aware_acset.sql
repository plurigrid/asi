-- Neighbor-Aware ACSet Extension Schema
-- Extends acset_history_view.sql with discohy relationships
--
-- Synergistic Triad: hatchery-papers (-1) ⊗ discohy-streams (0) ⊗ frontend-design (+1) = 0 ✓
-- Neighbor Graph: ACSet vertices connected to DiscoHy vertices via shared morphisms
--
-- Open ACSet Pattern: Compose via pushout (Catlab.jl Issue #89)
--   acset_history ←────┐
--                      ├──→ neighbor_graph (pushout)
--   discohy_history ←──┘

-- ═══════════════════════════════════════════════════════════════════════════════
-- DISCOHY HISTORY: Parallel view to acset_history
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE OR REPLACE VIEW discohy_history AS
SELECT 
  ROW_NUMBER() OVER (ORDER BY epoch_ms(timestamp::BIGINT)) as id,
  epoch_ms(timestamp::BIGINT) as timestamp,
  display::VARCHAR as display,
  COALESCE(project::VARCHAR, 'unknown') as project,
  CASE 
    WHEN LOWER(display::VARCHAR) LIKE '%error%' OR LOWER(display::VARCHAR) LIKE '%fail%' THEN -1
    WHEN LOWER(display::VARCHAR) LIKE '%create%' OR LOWER(display::VARCHAR) LIKE '%generate%' OR LOWER(display::VARCHAR) LIKE '%success%' THEN 1
    ELSE 0
  END as trit,
  -- GF(3) rolling sum
  SUM(CASE 
    WHEN LOWER(display::VARCHAR) LIKE '%error%' OR LOWER(display::VARCHAR) LIKE '%fail%' THEN -1
    WHEN LOWER(display::VARCHAR) LIKE '%create%' OR LOWER(display::VARCHAR) LIKE '%generate%' OR LOWER(display::VARCHAR) LIKE '%success%' THEN 1
    ELSE 0
  END) OVER (ORDER BY epoch_ms(timestamp::BIGINT) ROWS BETWEEN 2 PRECEDING AND CURRENT ROW) % 3 as gf3_sum,
  -- Skill domain classification
  CASE 
    WHEN LOWER(display::VARCHAR) LIKE '%diagram%' OR LOWER(display::VARCHAR) LIKE '%box%' THEN 'categorical'
    WHEN LOWER(display::VARCHAR) LIKE '%color%' OR LOWER(display::VARCHAR) LIKE '%stream%' THEN 'streaming'
    WHEN LOWER(display::VARCHAR) LIKE '%sexp%' OR LOWER(display::VARCHAR) LIKE '%parallel%' THEN 'parallel'
    WHEN LOWER(display::VARCHAR) LIKE '%neural%' OR LOWER(display::VARCHAR) LIKE '%wiring%' THEN 'neural'
    ELSE 'generic'
  END as discohy_type
FROM read_json_auto('/Users/bob/.claude/history.jsonl')
WHERE LOWER(display::VARCHAR) LIKE '%discohy%' 
   OR LOWER(display::VARCHAR) LIKE '%discopy%'
   OR LOWER(display::VARCHAR) LIKE '%hy lang%'
   OR LOWER(display::VARCHAR) LIKE '%categorical%stream%'
   OR LOWER(display::VARCHAR) LIKE '%sexp%traversal%';

-- ═══════════════════════════════════════════════════════════════════════════════
-- DISCOHY TRIT SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE OR REPLACE VIEW discohy_trit_summary AS
SELECT 
  trit,
  CASE trit WHEN -1 THEN 'MINUS' WHEN 0 THEN 'ERGODIC' WHEN 1 THEN 'PLUS' END as polarity,
  CASE trit WHEN -1 THEN '#2626D8' WHEN 0 THEN '#26D826' WHEN 1 THEN '#D82626' END as color,
  COUNT(*) as count,
  ROUND(COUNT(*) * 100.0 / SUM(COUNT(*)) OVER (), 2) as percentage
FROM discohy_history
GROUP BY trit
ORDER BY trit;

-- ═══════════════════════════════════════════════════════════════════════════════
-- NEIGHBOR GRAPH: ACSet ←→ DiscoHy relationships
-- Vertices: entries from both domains
-- Edges: temporal proximity + shared keywords → morphism strength
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE OR REPLACE VIEW neighbor_graph AS
WITH acset_entries AS (
  SELECT 
    'A' || CAST(id AS VARCHAR) as vertex_id,
    'acset' as domain,
    id,
    timestamp,
    display,
    trit,
    gf3_sum
  FROM acset_history
),
discohy_entries AS (
  SELECT 
    'D' || CAST(id AS VARCHAR) as vertex_id,
    'discohy' as domain,
    id,
    timestamp,
    display,
    trit,
    gf3_sum
  FROM discohy_history
),
all_vertices AS (
  SELECT * FROM acset_entries
  UNION ALL
  SELECT * FROM discohy_entries
),
-- Edge construction: connect entries within 10-minute window
edges AS (
  SELECT 
    a.vertex_id as src,
    d.vertex_id as tgt,
    a.domain as src_domain,
    d.domain as tgt_domain,
    a.trit as src_trit,
    d.trit as tgt_trit,
    (a.trit + d.trit) % 3 as edge_gf3,
    ABS(EXTRACT(EPOCH FROM (a.timestamp - d.timestamp))) as time_delta_seconds,
    -- Morphism strength: closer in time = stronger
    CASE 
      WHEN ABS(EXTRACT(EPOCH FROM (a.timestamp - d.timestamp))) < 60 THEN 1.0
      WHEN ABS(EXTRACT(EPOCH FROM (a.timestamp - d.timestamp))) < 300 THEN 0.7
      WHEN ABS(EXTRACT(EPOCH FROM (a.timestamp - d.timestamp))) < 600 THEN 0.4
      ELSE 0.1
    END as morphism_strength
  FROM acset_entries a
  CROSS JOIN discohy_entries d
  WHERE ABS(EXTRACT(EPOCH FROM (a.timestamp - d.timestamp))) < 600  -- 10 min window
)
SELECT 
  src,
  tgt,
  src_domain,
  tgt_domain,
  src_trit,
  tgt_trit,
  edge_gf3,
  time_delta_seconds,
  morphism_strength,
  -- Synergistic check: does this edge contribute to GF(3) conservation?
  CASE 
    WHEN (src_trit + tgt_trit) % 3 = 0 THEN true
    ELSE false
  END as synergistic_edge
FROM edges
ORDER BY morphism_strength DESC, time_delta_seconds ASC;

-- ═══════════════════════════════════════════════════════════════════════════════
-- NEIGHBOR SUMMARY: Statistics on the neighbor graph
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE OR REPLACE VIEW neighbor_summary AS
SELECT 
  COUNT(*) as total_edges,
  SUM(CASE WHEN synergistic_edge THEN 1 ELSE 0 END) as synergistic_edges,
  ROUND(SUM(CASE WHEN synergistic_edge THEN 1 ELSE 0 END) * 100.0 / NULLIF(COUNT(*), 0), 2) as synergistic_pct,
  AVG(morphism_strength) as avg_morphism_strength,
  MIN(time_delta_seconds) as min_time_delta,
  MAX(time_delta_seconds) as max_time_delta
FROM neighbor_graph;

-- ═══════════════════════════════════════════════════════════════════════════════
-- OPEN ACSET PORTS: Exposed vertices for composition
-- These are the "interfaces" that can be composed with other ACSets
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE OR REPLACE VIEW acset_ports AS
SELECT 
  vertex_id,
  domain,
  trit,
  display,
  -- Port type based on position and connectivity
  CASE 
    WHEN trit = -1 THEN 'input'   -- Validators receive
    WHEN trit = 1 THEN 'output'   -- Generators emit
    ELSE 'bidirectional'          -- Coordinators transport
  END as port_type,
  -- Count connections in neighbor graph
  (SELECT COUNT(*) FROM neighbor_graph WHERE src = all_v.vertex_id OR tgt = all_v.vertex_id) as degree
FROM (
  SELECT 'A' || CAST(id AS VARCHAR) as vertex_id, 'acset' as domain, trit, display FROM acset_history
  UNION ALL
  SELECT 'D' || CAST(id AS VARCHAR) as vertex_id, 'discohy' as domain, trit, display FROM discohy_history
) all_v
ORDER BY degree DESC;

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRIADIC NEIGHBORS: Find neighbor triads that conserve GF(3)
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE OR REPLACE VIEW neighbor_triads AS
WITH all_entries AS (
  SELECT 
    ROW_NUMBER() OVER (ORDER BY timestamp) as global_seq,
    vertex_id,
    domain,
    timestamp,
    trit,
    display
  FROM (
    SELECT 'A' || CAST(id AS VARCHAR) as vertex_id, 'acset' as domain, timestamp, trit, display FROM acset_history
    UNION ALL
    SELECT 'D' || CAST(id AS VARCHAR) as vertex_id, 'discohy' as domain, timestamp, trit, display FROM discohy_history
  ) combined
),
triad_groups AS (
  SELECT 
    CAST((global_seq - 1) / 3 + 1 AS INTEGER) as triad_id,
    vertex_id,
    domain,
    trit,
    SUBSTRING(display, 1, 40) as display_short
  FROM all_entries
)
SELECT 
  triad_id,
  LIST(vertex_id ORDER BY vertex_id) as vertices,
  LIST(domain ORDER BY vertex_id) as domains,
  LIST(trit ORDER BY vertex_id) as trits,
  SUM(trit) as trit_sum,
  SUM(trit) % 3 = 0 as gf3_conserved,
  -- Is this a mixed triad (both acset and discohy)?
  COUNT(DISTINCT domain) > 1 as is_mixed_triad
FROM triad_groups
GROUP BY triad_id
ORDER BY triad_id;

-- ═══════════════════════════════════════════════════════════════════════════════
-- MIXED TRIADS: Only triads containing both acset AND discohy entries
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE OR REPLACE VIEW mixed_triads AS
SELECT * FROM neighbor_triads
WHERE is_mixed_triad = true
ORDER BY triad_id;

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSERVATION CHECK: Overall GF(3) conservation statistics
-- ═══════════════════════════════════════════════════════════════════════════════

CREATE OR REPLACE VIEW neighbor_gf3_check AS
SELECT 
  'all_triads' as scope,
  COUNT(*) as total,
  SUM(CASE WHEN gf3_conserved THEN 1 ELSE 0 END) as conserved,
  ROUND(SUM(CASE WHEN gf3_conserved THEN 1 ELSE 0 END) * 100.0 / NULLIF(COUNT(*), 0), 2) as conservation_pct
FROM neighbor_triads
UNION ALL
SELECT 
  'mixed_triads' as scope,
  COUNT(*) as total,
  SUM(CASE WHEN gf3_conserved THEN 1 ELSE 0 END) as conserved,
  ROUND(SUM(CASE WHEN gf3_conserved THEN 1 ELSE 0 END) * 100.0 / NULLIF(COUNT(*), 0), 2) as conservation_pct
FROM mixed_triads;
