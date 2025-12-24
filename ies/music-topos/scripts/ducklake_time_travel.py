#!/usr/bin/env python3
"""
DuckLake Time-Travel Query Tool

Query threads across time with full version history.

Usage:
    python scripts/ducklake_time_travel.py snapshots           # List snapshots
    python scripts/ducklake_time_travel.py find <thread_id>    # Find thread at all versions
    python scripts/ducklake_time_travel.py changes <v1> <v2>   # Show changes between versions
    python scripts/ducklake_time_travel.py at <version> <query> # Query at version
"""

import sys
from pathlib import Path
import duckdb

DUCKLAKE_PATH = Path(__file__).parent.parent / "lib" / "amp_threads.ducklake"

def get_conn():
    conn = duckdb.connect()
    conn.execute("LOAD ducklake")
    conn.execute(f"ATTACH 'ducklake:{DUCKLAKE_PATH}' AS amp_lake")
    return conn

def list_snapshots(limit=20):
    conn = get_conn()
    print("Recent snapshots:")
    results = conn.execute(f"""
        SELECT snapshot_id, snapshot_time, changes 
        FROM ducklake_snapshots('amp_lake') 
        ORDER BY snapshot_id DESC 
        LIMIT {limit}
    """).fetchall()
    for r in results:
        print(f"  v{r[0]}: {r[1]} - {r[2]}")
    total = conn.execute("SELECT COUNT(*) FROM ducklake_snapshots('amp_lake')").fetchone()[0]
    print(f"\nTotal: {total:,} snapshots")

def find_thread(thread_id):
    conn = get_conn()
    
    # Current
    current = conn.execute(f"""
        SELECT thread_id, title, gay_color, gf3_trit, message_count
        FROM amp_lake.threads
        WHERE thread_id LIKE '%{thread_id}%'
        LIMIT 5
    """).fetchall()
    
    if not current:
        print(f"No thread found matching: {thread_id}")
        return
    
    print("Current state:")
    for r in current:
        print(f"  {r[0]}")
        print(f"    Title: {r[1]}")
        print(f"    Color: {r[2]} (trit={r[3]})")
        print(f"    Messages: {r[4]}")
    
    # Find all changes to this thread
    print("\nHistory (last 10 changes):")
    max_snap = conn.execute("SELECT MAX(snapshot_id) FROM ducklake_snapshots('amp_lake')").fetchone()[0]
    for r in current:
        tid = r[0]
        changes = conn.execute(f"""
            SELECT snapshot_id, change_type, title
            FROM ducklake_table_changes('amp_lake', 'main', 'threads', 1, {max_snap})
            WHERE thread_id = '{tid}'
            ORDER BY snapshot_id DESC
            LIMIT 10
        """).fetchall()
        for c in changes:
            print(f"  v{c[0]}: {c[1]} - {c[2][:50]}...")

def show_changes(v1, v2):
    conn = get_conn()
    print(f"Changes between v{v1} and v{v2}:")
    
    changes = conn.execute(f"""
        SELECT snapshot_id, change_type, thread_id, title
        FROM ducklake_table_changes('amp_lake', 'main', 'threads', {v1}, {v2})
        LIMIT 50
    """).fetchall()
    
    for c in changes:
        print(f"  v{c[0]} {c[1]}: {c[2][:30]}... - {c[3][:40]}...")

def query_at_version(version, query_part=""):
    conn = get_conn()
    
    sql = f"""
        SELECT thread_id, title, gay_color, gf3_trit
        FROM amp_lake.threads AT (VERSION => {version})
        {query_part}
        LIMIT 20
    """
    
    print(f"Query at version {version}:")
    results = conn.execute(sql).fetchall()
    for r in results:
        trit_sym = {-1: '⊖', 0: '○', 1: '⊕'}.get(r[3], '?')
        print(f"  {trit_sym} {r[2]} {r[0][:30]}...")
        print(f"      {r[1][:60]}")

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    
    cmd = sys.argv[1]
    
    if cmd == "snapshots":
        list_snapshots()
    elif cmd == "find" and len(sys.argv) > 2:
        find_thread(sys.argv[2])
    elif cmd == "changes" and len(sys.argv) > 3:
        show_changes(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "at" and len(sys.argv) > 2:
        version = int(sys.argv[2])
        query = " ".join(sys.argv[3:]) if len(sys.argv) > 3 else ""
        query_at_version(version, query)
    else:
        print(__doc__)

if __name__ == "__main__":
    main()
