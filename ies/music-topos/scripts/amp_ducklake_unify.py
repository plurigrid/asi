#!/usr/bin/env python3
"""
Amp Unified DuckLake - ACSet-based lakehouse for thread provenance across machines.

DuckLake: SQL database for metadata + Parquet files for data
- Uses local SQLite catalog (lib/amp_threads.ducklake/) 
- Stores data as Parquet in lib/amp_threads_data/
- ACSet schema with GF(3) coloring preserved

ACSet Objects:
  Machine::Ob     - source machines (local, hatchery, etc.)
  Thread::Ob      - thread metadata with Gay.jl colors
  Message::Ob     - messages within threads
  ThreadMachine   - join table for provenance (many-to-many)

Morphisms:
  thread_machine : ThreadMachine → Machine
  thread_ref     : ThreadMachine → Thread  
  message_thread : Message → Thread
"""

import os
import sys
import json
import hashlib
from datetime import datetime
from pathlib import Path
import duckdb

# SplitMix64 for deterministic coloring
GOLDEN = 0x9E3779B97F4A7C15
MIX1 = 0xBF58476D1CE4E5B9
MIX2 = 0x94D049BB133111EB
MASK64 = 0xFFFFFFFFFFFFFFFF

def splitmix64(seed: int) -> tuple[int, int]:
    state = (seed + GOLDEN) & MASK64
    z = state
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    z = z ^ (z >> 31)
    return state, z

def seed_from_string(s: str) -> int:
    raw = int(hashlib.sha256(s.encode()).hexdigest()[:16], 16)
    return raw & 0x7FFFFFFFFFFFFFFF

def color_from_seed(seed: int) -> dict:
    _, z = splitmix64(seed)
    hue = z % 360
    if hue < 60 or hue >= 300:
        trit = 1
    elif hue < 180:
        trit = 0
    else:
        trit = -1
    h = hue / 360.0
    s, l = 0.7, 0.55
    c = (1 - abs(2 * l - 1)) * s
    x = c * (1 - abs((h * 6) % 2 - 1))
    m = l - c / 2
    h6 = int(h * 6)
    if h6 == 0: r, g, b = c, x, 0
    elif h6 == 1: r, g, b = x, c, 0
    elif h6 == 2: r, g, b = 0, c, x
    elif h6 == 3: r, g, b = 0, x, c
    elif h6 == 4: r, g, b = x, 0, c
    else: r, g, b = c, 0, x
    hex_color = '#{:02X}{:02X}{:02X}'.format(
        int((r + m) * 255), int((g + m) * 255), int((b + m) * 255))
    return {'hue': hue, 'trit': trit, 'hex': hex_color, 'seed': seed}

def main():
    print("=" * 70)
    print("  AMP UNIFIED DUCKLAKE - ACSet Lakehouse")
    print("=" * 70)
    
    lib_dir = Path(__file__).parent.parent / "lib"
    ducklake_catalog = lib_dir / "amp_threads.ducklake"
    source_db = lib_dir / "amp_unified_lake.duckdb"
    
    # Remove existing catalog for fresh start
    if ducklake_catalog.exists():
        ducklake_catalog.unlink()
    
    print(f"\n[1/6] Creating DuckLake catalog at {ducklake_catalog}")
    
    # Connect to DuckDB and load ducklake extension
    conn = duckdb.connect()
    conn.execute("INSTALL ducklake FROM core")
    conn.execute("LOAD ducklake")
    
    # Create DuckLake with local SQLite catalog (data stored alongside)
    conn.execute(f"""
        ATTACH 'ducklake:{ducklake_catalog}' AS amp_lake
    """)
    
    print(f"      Catalog: {ducklake_catalog}")
    
    # Create ACSet schema
    print("\n[2/6] Creating ACSet schema...")
    
    # DuckLake doesn't support PRIMARY KEY constraints - we'll use unique values
    conn.execute("""
        CREATE TABLE amp_lake.machines (
            machine_id VARCHAR,
            hostname VARCHAR,
            description VARCHAR,
            seed BIGINT,
            gay_color VARCHAR,
            gf3_trit INTEGER
        )
    """)
    
    conn.execute("""
        CREATE TABLE amp_lake.threads (
            thread_id VARCHAR,
            title VARCHAR,
            author VARCHAR,
            repo VARCHAR,
            created_at TIMESTAMP,
            updated_at TIMESTAMP,
            message_count INTEGER,
            seed BIGINT,
            gay_color VARCHAR,
            gf3_trit INTEGER,
            synced_at TIMESTAMP
        )
    """)
    
    conn.execute("""
        CREATE TABLE amp_lake.thread_machines (
            thread_id VARCHAR,
            machine_id VARCHAR,
            synced_at TIMESTAMP
        )
    """)
    
    conn.execute("""
        CREATE TABLE amp_lake.messages (
            message_id VARCHAR,
            thread_id VARCHAR,
            role VARCHAR,
            content VARCHAR,
            created_at TIMESTAMP,
            sequence_num INTEGER,
            seed BIGINT,
            gay_color VARCHAR,
            gf3_trit INTEGER
        )
    """)
    
    # Create sync_log for temporal versioning
    conn.execute("""
        CREATE TABLE amp_lake.sync_log (
            sync_id INTEGER,
            synced_at TIMESTAMP,
            threads_added INTEGER,
            threads_updated INTEGER,
            messages_added INTEGER,
            source VARCHAR,
            gf3_sum INTEGER
        )
    """)
    
    print("      Created: machines, threads, thread_machines, messages, sync_log")
    
    # Load from source database
    print(f"\n[3/6] Loading from {source_db}...")
    
    source = duckdb.connect(str(source_db), read_only=True)
    
    # Get machines
    machines = source.execute("SELECT * FROM machines").fetchall()
    print(f"      Machines: {len(machines)}")
    
    for m in machines:
        conn.execute("""
            INSERT INTO amp_lake.machines VALUES (?, ?, ?, ?, ?, ?)
        """, [m[0], m[1], m[2], m[3], m[4], m[5]])
    
    # Get threads
    threads = source.execute("""
        SELECT thread_id, title, NULL as author, NULL as repo, 
               created_at, NULL as updated_at, message_count,
               seed, gay_color, gf3_trit, created_at as synced_at
        FROM threads
    """).fetchall()
    print(f"      Threads: {len(threads)}")
    
    for t in threads:
        conn.execute("""
            INSERT INTO amp_lake.threads VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, list(t))
    
    # Get thread-machine relationships
    tm_count = source.execute("SELECT COUNT(*) FROM thread_machines").fetchone()[0]
    print(f"      Thread-Machine relations: {tm_count}")
    
    thread_machines = source.execute("SELECT * FROM thread_machines").fetchall()
    for tm in thread_machines:
        conn.execute("""
            INSERT INTO amp_lake.thread_machines VALUES (?, ?, ?)
        """, [tm[0], tm[1], tm[2]])
    
    # Get messages with full content
    msg_count = source.execute("SELECT COUNT(*) FROM messages").fetchone()[0]
    print(f"      Messages: {msg_count}")
    
    messages = source.execute("""
        SELECT message_id, thread_id, role, content, created_at,
               sequence_num, seed, gay_color, gf3_trit
        FROM messages
    """).fetchall()
    
    batch_size = 5000
    for i in range(0, len(messages), batch_size):
        batch = messages[i:i+batch_size]
        for m in batch:
            conn.execute("""
                INSERT INTO amp_lake.messages VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, list(m))
        print(f"      Inserted {min(i+batch_size, len(messages))}/{len(messages)} messages...")
    
    source.close()
    
    # Create views
    print("\n[4/6] Creating ACSet views...")
    
    conn.execute("""
        CREATE VIEW amp_lake.thread_provenance AS
        SELECT 
            t.thread_id,
            t.title,
            t.gay_color,
            t.gf3_trit,
            t.message_count,
            ARRAY_AGG(tm.machine_id) as machines,
            COUNT(tm.machine_id) as machine_count
        FROM amp_lake.threads t
        JOIN amp_lake.thread_machines tm ON t.thread_id = tm.thread_id
        GROUP BY t.thread_id, t.title, t.gay_color, t.gf3_trit, t.message_count
    """)
    
    conn.execute("""
        CREATE VIEW amp_lake.gf3_by_machine AS
        SELECT 
            m.machine_id,
            m.hostname,
            t.gf3_trit,
            COUNT(*) as count
        FROM amp_lake.machines m
        JOIN amp_lake.thread_machines tm ON m.machine_id = tm.machine_id
        JOIN amp_lake.threads t ON tm.thread_id = t.thread_id
        GROUP BY m.machine_id, m.hostname, t.gf3_trit
    """)
    
    conn.execute("""
        CREATE VIEW amp_lake.overlap_threads AS
        SELECT 
            t.thread_id,
            t.title,
            t.gay_color,
            t.gf3_trit,
            t.message_count
        FROM amp_lake.thread_provenance t
        WHERE t.machine_count = 2
    """)
    
    print("      Created: thread_provenance, gf3_by_machine, overlap_threads")
    
    # Verify GF(3) conservation
    print("\n[5/6] Verifying GF(3) conservation...")
    
    gf3_stats = conn.execute("""
        SELECT gf3_trit, COUNT(*) 
        FROM amp_lake.threads 
        GROUP BY gf3_trit 
        ORDER BY gf3_trit
    """).fetchall()
    
    balance = {-1: 0, 0: 0, 1: 0}
    for row in gf3_stats:
        if row[0] is not None:
            balance[row[0]] = row[1]
    
    gf3_sum = balance[-1] * -1 + balance[1] * 1
    conserved = gf3_sum % 3 == 0
    
    print(f"      ⊕ PLUS:    {balance[1]:,}")
    print(f"      ○ ERGODIC: {balance[0]:,}")
    print(f"      ⊖ MINUS:   {balance[-1]:,}")
    print(f"      Σ Sum: {gf3_sum}, mod 3: {gf3_sum % 3}")
    print(f"      Conservation: {'✓ CONSERVED' if conserved else '✗ NOT CONSERVED'}")
    
    # Log sync
    conn.execute("""
        INSERT INTO amp_lake.sync_log (sync_id, synced_at, threads_added, messages_added, source, gf3_sum)
        VALUES (1, CURRENT_TIMESTAMP, ?, ?, 'ducklake_unify', ?)
    """, [len(threads), len(messages), gf3_sum % 3])
    
    # Final statistics
    print("\n[6/6] DuckLake statistics...")
    
    final_stats = {
        'threads': conn.execute("SELECT COUNT(*) FROM amp_lake.threads").fetchone()[0],
        'messages': conn.execute("SELECT COUNT(*) FROM amp_lake.messages").fetchone()[0],
        'machines': conn.execute("SELECT COUNT(*) FROM amp_lake.machines").fetchone()[0],
        'relations': conn.execute("SELECT COUNT(*) FROM amp_lake.thread_machines").fetchone()[0],
        'overlap': conn.execute("SELECT COUNT(*) FROM amp_lake.overlap_threads").fetchone()[0]
    }
    
    print("\n" + "=" * 70)
    print("  DUCKLAKE UNIFIED STATISTICS")
    print("=" * 70)
    print(f"  Threads:           {final_stats['threads']:,}")
    print(f"  Messages:          {final_stats['messages']:,}")
    print(f"  Machines:          {final_stats['machines']}")
    print(f"  Relations:         {final_stats['relations']:,}")
    print(f"  Overlap (both):    {final_stats['overlap']}")
    print(f"\n  Catalog: {ducklake_catalog}")
    
    # Show data directory size
    ducklake_data = ducklake_catalog.parent / (ducklake_catalog.stem + "_data")
    if ducklake_data.exists():
        parquet_files = list(ducklake_data.glob("**/*.parquet"))
        if parquet_files:
            print(f"\n  Parquet files: {len(parquet_files)}")
            for pf in parquet_files[:5]:
                size = pf.stat().st_size
                print(f"    {pf.name}: {size:,} bytes")
    
    print("\n" + "=" * 70)
    print("  ACSet MORPHISMS (Relationships)")
    print("=" * 70)
    print("""
    thread_machines : Thread × Machine  (many-to-many provenance)
    messages        : Message → Thread  (message belongs to thread)
    
    Views:
      • thread_provenance: ARRAY_AGG(machines) per thread
      • gf3_by_machine:    Trit distribution by machine
      • overlap_threads:   Threads on BOTH machines (24 total)
    
    Query example:
      SELECT * FROM amp_lake.overlap_threads ORDER BY message_count DESC;
    """)
    
    conn.close()
    print("\n✓ DuckLake unified successfully!")

if __name__ == "__main__":
    main()
