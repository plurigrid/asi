#!/usr/bin/env python3
"""
Live Thread Ingestion - Query threads and update the Unified Thread Lake
Run this to refresh the database with latest thread data
"""
import duckdb
import json
import re
import time
import subprocess
import sys

DB_PATH = '/Users/bob/ies/music-topos/lib/unified_thread_lake.duckdb'

# Concept extraction patterns
PATTERNS = {
    'skill': r'\bskill\b',
    'MCP': r'\bmcp\b',
    'subagent': r'\bsubagent\b',
    'thread': r'\bthread\b',
    'DuckDB': r'\bduckdb\b',
    'ACSet': r'\bacset\b',
    'GF3': r'\bgf\(?3\)?|ternary|3-color',
    'parallelism': r'\bparallel\b|\bspi\b',
    'Babashka': r'\bbabashka\b',
    'Clojure': r'\bclj\b|\bclojure\b',
    'topos': r'\btopos\b|\bgeometric\b',
    'WORLD': r'\bworld\b|\bunworld\b',
    'entropy': r'\bentropy\b',
    'relational': r'\brelational\b',
    'HyJAX': r'\bhyjax\b',
    'alife': r'\balife\b',
    'codex': r'\bcodex\b',
    'discohy': r'\bdiscohy\b',
    'LocalSend': r'\blocalsend\b',
    'Synadia': r'\bsynadia\b|\bnats\b',
    'spectral': r'\bspectral\b',
    'Gay': r'\bgay\.jl\b|\bgay\b',
    'operad': r'\boperad\b',
    'morphism': r'\bmorphism\b',
    'pullback': r'\bpullback\b',
    'ColoredShape': r'\bcolored\s*shape\b',
}


def extract_concepts(text: str) -> list:
    """Extract concepts from text"""
    found = []
    text_lower = text.lower()
    for concept, pattern in PATTERNS.items():
        if re.search(pattern, text_lower):
            found.append(concept)
    return found


def ingest_threads(threads: list, conn):
    """Ingest thread list into database"""
    concept_freq = {}
    concept_relations = {}
    
    for t in threads:
        tid = t.get('id', '')
        title = t.get('title', '')
        msg_count = t.get('messageCount', 0)
        
        # Insert thread
        conn.execute("""
            INSERT OR REPLACE INTO threads VALUES (?, ?, ?, CURRENT_TIMESTAMP)
        """, [tid, title, msg_count])
        
        # Extract concepts
        concepts = extract_concepts(title)
        for c in concepts:
            if c not in concept_freq:
                concept_freq[c] = 0
            concept_freq[c] += 1
            
            # Link thread to concept
            conn.execute("""
                INSERT OR IGNORE INTO thread_concept_links VALUES (?, ?)
            """, [tid, f"concept:{c}"])
        
        # Add co-occurrence relations
        for i, c1 in enumerate(concepts):
            for c2 in concepts[i+1:]:
                key = (c1, c2) if c1 < c2 else (c2, c1)
                if key not in concept_relations:
                    concept_relations[key] = 0
                concept_relations[key] += 1
    
    # Update concepts
    for name, freq in concept_freq.items():
        conn.execute("""
            INSERT INTO concepts VALUES (?, ?, ?, ?)
            ON CONFLICT(concept_id) DO UPDATE SET 
                frequency = concepts.frequency + excluded.frequency
        """, [f"concept:{name}", name, freq, freq])
    
    # Update relations
    for (c1, c2), weight in concept_relations.items():
        conn.execute("""
            INSERT INTO concept_relations VALUES (?, ?, 'co-occurs', ?)
            ON CONFLICT(from_concept, to_concept) DO UPDATE SET
                weight = concept_relations.weight + excluded.weight
        """, [c1, c2, weight])
    
    return len(threads), len(concept_freq), len(concept_relations)


def main():
    print("="*60)
    print("  LIVE THREAD INGESTION")
    print("="*60)
    
    # Sample new threads to ingest (in real usage, this would come from find_thread)
    NEW_THREADS = [
        {"id": "T-019b4424-7b9e-7515-bb83-5514e2aefba8", "title": "Exploring relational thinking with HyJAX skills", "messageCount": 50},
        {"id": "T-019b4417-c005-743b-8a4c-1b87bcfc806f", "title": "Maximally polarizing implied worlds along subagent directions", "messageCount": 80},
        {"id": "T-new-001", "title": "New skill for entropy and spectral analysis", "messageCount": 25},
        {"id": "T-new-002", "title": "ACSet morphism pullback queries in DuckDB", "messageCount": 30},
        {"id": "T-new-003", "title": "Gay.jl GF3 coloring for parallel MCP subagents", "messageCount": 45},
    ]
    
    # Connect
    conn = duckdb.connect(DB_PATH)
    
    # Ensure schema
    conn.execute("""
        CREATE TABLE IF NOT EXISTS thread_concept_links (
            thread_id VARCHAR,
            concept_id VARCHAR,
            PRIMARY KEY (thread_id, concept_id)
        )
    """)
    
    # Ingest
    print("\n[1] Ingesting threads...")
    n_threads, n_concepts, n_relations = ingest_threads(NEW_THREADS, conn)
    print(f"    Ingested: {n_threads} threads, {n_concepts} concepts, {n_relations} relations")
    
    # Report
    print("\n[2] Updated database state:")
    
    result = conn.execute("SELECT COUNT(*) FROM threads").fetchone()
    print(f"    Total threads: {result[0]}")
    
    result = conn.execute("SELECT COUNT(*) FROM concepts").fetchone()
    print(f"    Total concepts: {result[0]}")
    
    result = conn.execute("SELECT COUNT(*) FROM concept_relations").fetchone()
    print(f"    Total relations: {result[0]}")
    
    # Top concepts
    print("\n[3] Top concepts by frequency:")
    for row in conn.execute("""
        SELECT name, frequency FROM concepts ORDER BY frequency DESC LIMIT 8
    """).fetchall():
        print(f"    {row[0]:15} {row[1]}")
    
    # New paths
    print("\n[4] Concept paths:")
    for row in conn.execute("""
        SELECT from_concept || ' → ' || to_concept as edge, weight
        FROM concept_relations ORDER BY weight DESC LIMIT 8
    """).fetchall():
        print(f"    {row[0]:30} (w={row[1]})")
    
    conn.close()
    
    print("\n" + "="*60)
    print(f"  Database updated: {DB_PATH}")
    print("="*60 + "\n")


if __name__ == "__main__":
    main()
