#!/usr/bin/env python3
"""
Unified Thread Lake - Merge ThreadACSet with existing DuckLake
Creates a complete relational view of all thread data
"""
import duckdb
import json
import time

print("="*70)
print("  UNIFIED THREAD LAKE - Merging ACSet with DuckLake")
print("="*70)

# Connect to persistent DB
DB_PATH = '/Users/bob/ies/music-topos/lib/unified_thread_lake.duckdb'
conn = duckdb.connect(DB_PATH)

# Create schema
print("\n[1] Creating unified schema...")

conn.execute("""
CREATE TABLE IF NOT EXISTS threads (
    thread_id VARCHAR PRIMARY KEY,
    title VARCHAR,
    message_count INT,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
)
""")

conn.execute("""
CREATE TABLE IF NOT EXISTS concepts (
    concept_id VARCHAR PRIMARY KEY,
    name VARCHAR,
    frequency INT DEFAULT 0,
    hub_score INT DEFAULT 0
)
""")

conn.execute("""
CREATE TABLE IF NOT EXISTS thread_concept_links (
    thread_id VARCHAR,
    concept_id VARCHAR,
    PRIMARY KEY (thread_id, concept_id)
)
""")

conn.execute("""
CREATE TABLE IF NOT EXISTS concept_relations (
    from_concept VARCHAR,
    to_concept VARCHAR,
    relation_type VARCHAR DEFAULT 'co-occurs',
    weight INT DEFAULT 1,
    PRIMARY KEY (from_concept, to_concept)
)
""")

conn.execute("""
CREATE TABLE IF NOT EXISTS colored_sexprs (
    sexpr_id VARCHAR PRIMARY KEY,
    root_color VARCHAR,
    tree_json JSON,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
)
""")

# Load thread data
print("[2] Loading thread data...")

THREADS = [
    ("T-019b4417-c005-743b-8a4c-1b87bcfc806f", "Maximally polarizing implied worlds along subagent directions", 77),
    ("T-019b4424-7b9e-7515-bb83-5514e2aefba8", "Exploring relational thinking with HyJAX skills", 47),
    ("T-019b4405-2a14-7207-af89-748a784371d5", "Load localsend script", 306),
    ("T-019b4412-7cbf-705c-81e8-1b84fb6d49c3", "Use alife skill with Exa MCP for refined queries", 59),
    ("T-019b43f1-cae1-7043-9196-c6839793df4c", "List of active workspace threads", 112),
    ("T-019b43f9-f76d-771f-b361-59e94bc175e6", "Load all the most bizarre skills", 108),
    ("T-019b43de-907c-7008-a545-57e8ff698498", "Random walk spectral gap refinement process", 104),
    ("T-019b43b8-a9e6-7109-8142-74c4e95f725a", "DuckDB time travel queries for November 2025", 151),
    ("T-019b43a6-11f7-77a8-a9cd-ea618e457b70", "Load acset skill", 88),
    ("T-019b438f-c843-7779-8812-bc0d6fe8b803", "Continue synergistic skill triads and subagent coloring", 177),
    ("T-019b4334-885f-7395-9905-1bf90b48983f", "Unworld system GF(3) conservation and agent propagation", 116),
    ("T-019b42fd-3020-74f4-808b-331ec29b75c2", "Borkdude skill integration and goblin capability propagation", 141),
    ("T-019b42dd-588b-755f-b0dd-4b319ad6d7aa", "Maximum parallelism with SPI and SplitMixTernary", 116),
    ("T-019b42b1-e9cd-75c3-84c8-8c4de7c109fd", "Integrating transients, Babashka, and MCP for Codex", 143),
    ("T-019b428e-cf8e-72bd-8485-a59ca9e9e477", "Integrate Synadia broadcasts with WORLD system", 102),
    ("T-019b381e-cb1c-728e-973f-b8d2106767ed", "DiscoPy interaction entropy harmonizer across 17 subagents", 175),
]

for tid, title, msg_count in THREADS:
    conn.execute("""
        INSERT OR REPLACE INTO threads VALUES (?, ?, ?, CURRENT_TIMESTAMP)
    """, [tid, title, msg_count])

print(f"    Loaded {len(THREADS)} threads")

# Load concepts
print("[3] Loading concepts...")

CONCEPTS = [
    ("skill", 5, 8),
    ("subagent", 3, 3),
    ("MCP", 3, 4),
    ("GF3", 3, 5),
    ("LocalSend", 2, 2),
    ("ACSet", 2, 2),
    ("WORLD", 2, 1),
    ("codex", 2, 1),
    ("HyJAX", 1, 1),
    ("relational", 1, 1),
    ("entropy", 1, 1),
    ("DuckDB", 1, 1),
    ("Babashka", 1, 2),
    ("Clojure", 1, 3),
    ("topos", 1, 1),
    ("spectral", 1, 1),
    ("parallelism", 1, 1),
    ("discohy", 1, 1),
    ("alife", 1, 2),
]

for name, freq, hub in CONCEPTS:
    conn.execute("""
        INSERT OR REPLACE INTO concepts VALUES (?, ?, ?, ?)
    """, [f"concept:{name}", name, freq, hub])

print(f"    Loaded {len(CONCEPTS)} concepts")

# Load relations
print("[4] Loading concept relations...")

RELATIONS = [
    ("skill", "subagent", 2),
    ("skill", "MCP", 1),
    ("skill", "alife", 1),
    ("skill", "LocalSend", 1),
    ("skill", "ACSet", 1),
    ("HyJAX", "relational", 1),
    ("HyJAX", "entropy", 1),
    ("MCP", "alife", 1),
    ("MCP", "Babashka", 1),
    ("GF3", "coloring", 1),
    ("GF3", "parallelism", 1),
    ("ACSet", "discohy", 1),
    ("WORLD", "Synadia", 1),
    ("subagent", "LocalSend", 1),
    ("entropy", "spectral", 1),
]

for c1, c2, weight in RELATIONS:
    conn.execute("""
        INSERT OR REPLACE INTO concept_relations VALUES (?, ?, 'co-occurs', ?)
    """, [c1, c2, weight])

print(f"    Loaded {len(RELATIONS)} relations")

# Store colored s-expression
print("[5] Storing Colored S-expression...")

sexpr = {
    "root": "acset-gold",
    "children": [
        {"color": "threads-red", "count": len(THREADS)},
        {"color": "concepts-green", "count": len(CONCEPTS)},
        {"color": "relations-purple", "count": len(RELATIONS)}
    ]
}

conn.execute("""
    INSERT OR REPLACE INTO colored_sexprs VALUES (?, ?, ?, CURRENT_TIMESTAMP)
""", ["sexpr-main", "acset-gold", json.dumps(sexpr)])

# Run queries
print("\n" + "="*70)
print("  UNIFIED LAKE QUERIES")
print("="*70)

print("\n[A] Thread summary:")
result = conn.execute("""
    SELECT COUNT(*) as threads, SUM(message_count) as messages
    FROM threads
""").fetchone()
print(f"    {result[0]} threads, {result[1]} total messages")

print("\n[B] Top concepts by hub score:")
for row in conn.execute("""
    SELECT name, frequency, hub_score FROM concepts
    ORDER BY hub_score DESC LIMIT 8
""").fetchall():
    print(f"    {row[0]:15} freq={row[1]} hub={row[2]}")

print("\n[C] Concept network (strongest):")
for row in conn.execute("""
    SELECT from_concept, to_concept, weight FROM concept_relations
    ORDER BY weight DESC LIMIT 8
""").fetchall():
    print(f"    {row[0]:12} --{row[2]}--> {row[1]}")

print("\n[D] 2-hop reachability from 'skill':")
for row in conn.execute("""
    SELECT r1.to_concept as hop1, r2.to_concept as hop2
    FROM concept_relations r1
    JOIN concept_relations r2 ON r1.to_concept = r2.from_concept
    WHERE r1.from_concept = 'skill' AND r2.to_concept != 'skill'
""").fetchall():
    print(f"    skill → {row[0]} → {row[1]}")

print("\n[E] Colored S-expr summary:")
for row in conn.execute("""
    SELECT sexpr_id, root_color, tree_json FROM colored_sexprs
""").fetchall():
    data = json.loads(row[2])
    print(f"    {row[0]}: ({row[1]} ...)")
    for child in data.get('children', []):
        print(f"        ({child['color']} count={child['count']})")

# Save summary
print(f"\n[F] Database saved to: {DB_PATH}")

# Export view as SQL
print("[G] Exporting unified view...")

view_sql = """
-- Unified Thread Lake View
-- Generated: {timestamp}

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
""".format(timestamp=time.strftime('%Y-%m-%d %H:%M:%S'))

with open('/Users/bob/ies/music-topos/lib/unified_lake_views.sql', 'w') as f:
    f.write(view_sql)
print("    Saved: unified_lake_views.sql")

conn.close()

print("\n" + "="*70)
print("  UNIFIED THREAD LAKE COMPLETE")
print("="*70 + "\n")
