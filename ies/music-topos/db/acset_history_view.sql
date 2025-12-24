-- GeoACSet History Integration Schema
-- Queries ~/.claude/history.jsonl with GF(3) trit assignment
-- Supports refinement queries for ACSets.jl / GeoACSet.jl patterns
--
-- Synergistic Triad: clj-kondo-3color (-1) ⊗ acsets (0) ⊗ rama-gay-clojure (+1) = 0 ✓
-- Subagents: VALIDATOR (verify) | COORDINATOR (transport) | GENERATOR (create)

CREATE OR REPLACE VIEW acset_history AS
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
  -- GF(3) sum computed over rolling window
  SUM(CASE 
    WHEN LOWER(display::VARCHAR) LIKE '%error%' OR LOWER(display::VARCHAR) LIKE '%fail%' THEN -1
    WHEN LOWER(display::VARCHAR) LIKE '%create%' OR LOWER(display::VARCHAR) LIKE '%generate%' OR LOWER(display::VARCHAR) LIKE '%success%' THEN 1
    ELSE 0
  END) OVER (ORDER BY epoch_ms(timestamp::BIGINT) ROWS BETWEEN 2 PRECEDING AND CURRENT ROW) % 3 as gf3_sum
FROM read_json_auto('/Users/bob/.claude/history.jsonl')
WHERE LOWER(display::VARCHAR) LIKE '%acset%' 
   OR LOWER(display::VARCHAR) LIKE '%geoacset%'
   OR LOWER(display::VARCHAR) LIKE '%schema%'
   OR LOWER(display::VARCHAR) LIKE '%morphism%';

-- Refinement query: use as prepared statement instead of macro
-- Usage: SELECT * FROM acset_history WHERE LOWER(display) LIKE '%geoacset%';

-- Summary view for trit distribution
CREATE OR REPLACE VIEW acset_trit_summary AS
SELECT 
  trit,
  CASE trit WHEN -1 THEN 'MINUS' WHEN 0 THEN 'ERGODIC' WHEN 1 THEN 'PLUS' END as polarity,
  CASE trit WHEN -1 THEN '#2626D8' WHEN 0 THEN '#26D826' WHEN 1 THEN '#D82626' END as color,
  COUNT(*) as count,
  ROUND(COUNT(*) * 100.0 / SUM(COUNT(*)) OVER (), 2) as percentage
FROM acset_history
GROUP BY trit
ORDER BY trit;

-- GeoACSet pattern view: entries matching bmorphism/GeoACSet.jl patterns
CREATE OR REPLACE VIEW geoacset_patterns AS
SELECT 
  id,
  timestamp,
  display,
  trit,
  CASE 
    WHEN LOWER(display::VARCHAR) LIKE '%geoacset%' THEN 'geo'
    WHEN LOWER(display::VARCHAR) LIKE '%mesopacset%' THEN 'mesop'
    WHEN LOWER(display::VARCHAR) LIKE '%gayacset%' OR LOWER(display::VARCHAR) LIKE '%blessedgayseeds%' THEN 'gay'
    ELSE 'generic'
  END as acset_type
FROM acset_history
WHERE LOWER(display::VARCHAR) LIKE '%geoacset%'
   OR LOWER(display::VARCHAR) LIKE '%mesopacset%'
   OR LOWER(display::VARCHAR) LIKE '%gayacset%'
   OR LOWER(display::VARCHAR) LIKE '%blessedgayseeds%';

-- Triadic analysis: group entries by 3 for GF(3) conservation check
CREATE OR REPLACE VIEW acset_triads AS
WITH numbered AS (
  SELECT 
    ROW_NUMBER() OVER (ORDER BY id) as seq,
    id,
    SUBSTRING(display, 1, 60) as display_short,
    trit,
    CAST((ROW_NUMBER() OVER (ORDER BY id) - 1) / 3 + 1 AS INTEGER) as triad_group
  FROM acset_history
)
SELECT 
  triad_group as triad_id,
  LIST(id ORDER BY seq) as entry_ids,
  LIST(trit ORDER BY seq) as trits,
  SUM(trit) as trit_sum,
  SUM(trit) % 3 = 0 as gf3_conserved
FROM numbered
GROUP BY triad_group
ORDER BY triad_id;
