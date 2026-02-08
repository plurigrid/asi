
-- Unified Thread Lake View
-- Generated: 2025-12-21 22:58:39

-- Thread-Concept Projection
CREATE OR REPLACE VIEW thread_concept_matrix AS
SELECT 
    t.thread_id,
    t.title,
    t.message_count,
    c.name as concept,
    c.hub_score
FROM threads t
CROSS JOIN concepts c
WHERE t.title ILIKE '%' || c.name || '%';

-- Concept Hub Analysis
CREATE OR REPLACE VIEW concept_hubs AS
SELECT 
    c.name,
    c.frequency,
    c.hub_score,
    COUNT(r.to_concept) as outgoing_edges
FROM concepts c
LEFT JOIN concept_relations r ON c.name = r.from_concept
GROUP BY c.name, c.frequency, c.hub_score
ORDER BY c.hub_score DESC;

-- 2-Hop Paths
CREATE OR REPLACE VIEW concept_paths AS
SELECT 
    r1.from_concept as start,
    r1.to_concept as hop1,
    r2.to_concept as hop2,
    r1.weight + r2.weight as path_weight
FROM concept_relations r1
JOIN concept_relations r2 ON r1.to_concept = r2.from_concept
WHERE r1.from_concept != r2.to_concept;
