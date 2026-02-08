#!/usr/bin/env python3
"""
Query Thread Lake - CLI for HyJAX Thread Relational ACSet
Usage: uv run python query_thread_lake.py <command> [args]

Commands:
  concepts          - List top concepts with GF(3) coloring
  threads           - List threads by message count
  hubs              - Show concept hub scores
  paths <concept>   - Find 2-hop paths from a concept
  cluster <concept> - Find threads mentioning a concept
  sexpr             - Output Colored S-expression
  sql <query>       - Run raw SQL query
"""
import sys
import duckdb
import json

DB_PATH = '/Users/bob/ies/music-topos/lib/unified_thread_lake.duckdb'

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    
    cmd = sys.argv[1]
    conn = duckdb.connect(DB_PATH, read_only=True)
    
    if cmd == "concepts":
        print("=== TOP CONCEPTS (GF(3) colored) ===")
        for row in conn.execute('''
            SELECT name, frequency, gf3_trit, hub_score, gay_color 
            FROM concepts ORDER BY frequency DESC LIMIT 15
        ''').fetchall():
            trit = ['RED', 'YELLOW', 'BLUE'][row[2]]
            bar = '█' * min(row[1], 10)
            print(f"  {row[0]:15} {row[1]:2} {trit:6} hub={row[3]:2} {row[4]} {bar}")
    
    elif cmd == "threads":
        print("=== THREADS BY MESSAGE COUNT ===")
        for row in conn.execute('SELECT thread_id, title, message_count FROM threads ORDER BY message_count DESC LIMIT 15').fetchall():
            print(f"  {row[2]:3} msgs  {row[1][:55]}")
    
    elif cmd == "hubs":
        print("=== CONCEPT HUBS (most connected) ===")
        for row in conn.execute('SELECT name, hub_score, frequency FROM concepts ORDER BY hub_score DESC LIMIT 12').fetchall():
            print(f"  {row[0]:15} hub={row[1]:2} freq={row[2]}")
    
    elif cmd == "paths" and len(sys.argv) > 2:
        concept = sys.argv[2]
        print(f"=== 2-HOP PATHS FROM '{concept}' ===")
        paths = conn.execute("""
            SELECT r1.to_concept, r2.to_concept, r1.weight + r2.weight
            FROM concept_relations r1
            JOIN concept_relations r2 ON r1.to_concept = r2.from_concept
            WHERE r1.from_concept = ? AND r1.from_concept != r2.to_concept
            ORDER BY r1.weight + r2.weight DESC LIMIT 10
        """, [concept]).fetchall()
        for p in paths:
            print(f"  {concept} → {p[0]} → {p[1]} (w={p[2]})")
        if not paths:
            print(f"  No paths found from '{concept}'")
    
    elif cmd == "cluster" and len(sys.argv) > 2:
        concept = sys.argv[2]
        print(f"=== THREADS MENTIONING '{concept}' ===")
        threads = conn.execute("""
            SELECT t.title, t.message_count
            FROM threads t
            JOIN thread_concept_links l ON t.thread_id = l.thread_id
            WHERE l.concept_id = ?
            ORDER BY t.message_count DESC
        """, [f"concept:{concept}"]).fetchall()
        for t in threads:
            print(f"  {t[1]:3} msgs  {t[0][:60]}")
        if not threads:
            print(f"  No threads found for '{concept}'")
    
    elif cmd == "sexpr":
        print("(acset-gold")
        print(f"  (threads-red {conn.execute('SELECT COUNT(*) FROM threads').fetchone()[0]})")
        print("  (concepts-green")
        for gf3 in [0, 1, 2]:
            name = ['RED', 'YELLOW', 'BLUE'][gf3]
            cnt = conn.execute(f'SELECT COUNT(*) FROM concepts WHERE gf3_trit={gf3}').fetchone()[0]
            print(f"    ({name.lower()} {cnt})")
        print("  )")
        print(f"  (relations-purple {conn.execute('SELECT COUNT(*) FROM concept_relations').fetchone()[0]}))")
    
    elif cmd == "sql" and len(sys.argv) > 2:
        query = " ".join(sys.argv[2:])
        try:
            for row in conn.execute(query).fetchall():
                print(row)
        except Exception as e:
            print(f"Error: {e}")
    
    else:
        print(__doc__)
    
    conn.close()

if __name__ == "__main__":
    main()
