#!/usr/bin/env python3
"""Query ThreadACSet with DuckDB"""
import duckdb

conn = duckdb.connect(':memory:')

# Create tables
conn.execute("CREATE TABLE thread_concepts (thread_id VARCHAR, concept VARCHAR)")
conn.execute("CREATE TABLE concept_relations (concept_from VARCHAR, concept_to VARCHAR, weight INT)")

# Load data
with open('/Users/bob/ies/music-topos/lib/thread_full_export.sql', 'r') as f:
    for line in f:
        if line.startswith('INSERT'):
            try:
                conn.execute(line)
            except:
                pass

print("="*60)
print("  DUCKDB RELATIONAL QUERIES ON THREAD ACSET")
print("="*60)

# Query 1: Concept frequency
print("\n[1] CONCEPT FREQUENCY")
for row in conn.execute("""
    SELECT concept, COUNT(*) as n FROM thread_concepts 
    GROUP BY concept ORDER BY n DESC LIMIT 10
""").fetchall():
    print(f"    {row[0]:15} {row[1]} threads")

# Query 2: Hub concepts
print("\n[2] HUB CONCEPTS")
for row in conn.execute("""
    SELECT concept_from, SUM(weight) as w FROM concept_relations
    GROUP BY concept_from ORDER BY w DESC LIMIT 8
""").fetchall():
    print(f"    {row[0]:15} weight: {row[1]}")

# Query 3: Strongest relations
print("\n[3] STRONGEST CO-OCCURRENCES")
for row in conn.execute("""
    SELECT concept_from, concept_to, weight FROM concept_relations
    WHERE concept_from < concept_to ORDER BY weight DESC LIMIT 8
""").fetchall():
    print(f"    {row[0]:12} <--{row[2]}--> {row[1]}")

# Query 4: Concept clusters
print("\n[4] CONCEPT CLUSTERS (shared threads)")
for row in conn.execute("""
    SELECT a.concept, b.concept, COUNT(*) as shared
    FROM thread_concepts a
    JOIN thread_concepts b ON a.thread_id = b.thread_id AND a.concept < b.concept
    GROUP BY a.concept, b.concept ORDER BY shared DESC LIMIT 8
""").fetchall():
    print(f"    {row[0]:12} + {row[1]:12} = {row[2]} shared")

# Query 5: 2-hop paths from 'skill'
print("\n[5] 2-HOP PATHS FROM 'skill'")
for row in conn.execute("""
    SELECT r1.concept_to, r2.concept_to, r1.weight + r2.weight as w
    FROM concept_relations r1
    JOIN concept_relations r2 ON r1.concept_to = r2.concept_from
    WHERE r1.concept_from = 'skill' AND r2.concept_to != 'skill'
    ORDER BY w DESC LIMIT 5
""").fetchall():
    print(f"    skill → {row[0]} → {row[1]} (w={row[2]})")

print("\n" + "="*60)
conn.close()
