#!/usr/bin/env python3
"""
Ingest 1375+ Claude .jsonl history files into DuckLake
with ACSet mutual awareness graph and GF(3) coloring.

Usage: uv run --with duckdb python ~/worldnet/ingest_claude_to_ducklake.py

Triadic Pipeline:
  MINUS (-1): Validate & parse JSONL
  ERGODIC (0): Transform & extract edges
  PLUS (+1): Insert with play/coplay awareness
"""

import duckdb
import json
import os
import hashlib
from datetime import datetime
from pathlib import Path
from typing import Generator, Dict, Any, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor, as_completed

# Config
DUCKLAKE_PATH = Path.home() / "worldnet" / "cognition.duckdb"
CLAUDE_PROJECTS = Path.home() / ".claude" / "projects"
GAMMA = 0x9E3779B97F4A7C15

def gf3_from_seed(seed: int) -> int:
    """Derive GF(3) trit from seed using golden ratio hash."""
    h = (seed * GAMMA) & 0xFFFFFFFFFFFFFFFF
    return (h % 3) - 1  # Maps to {-1, 0, +1}

def gf3_from_string(s: str) -> int:
    """Derive trit from string via hash."""
    h = int(hashlib.sha256(s.encode()).hexdigest()[:16], 16)
    return gf3_from_seed(h)

def create_schema(con):
    """Create ACSet-style schema for Claude cognition."""
    con.execute("""
        CREATE TABLE IF NOT EXISTS messages (
            id VARCHAR PRIMARY KEY,
            session_id VARCHAR,
            parent_id VARCHAR,
            type VARCHAR,
            role VARCHAR,
            timestamp TIMESTAMP,
            cwd VARCHAR,
            git_branch VARCHAR,
            agent_id VARCHAR,
            model VARCHAR,
            content_preview VARCHAR,
            trit INTEGER,
            ingested_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    """)
    
    con.execute("""
        CREATE TABLE IF NOT EXISTS sessions (
            session_id VARCHAR PRIMARY KEY,
            project_path VARCHAR,
            file_path VARCHAR,
            first_message_at TIMESTAMP,
            last_message_at TIMESTAMP,
            message_count INTEGER DEFAULT 0,
            trit INTEGER,
            ingested_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    """)
    
    # ACSet: play/coplay edges for mutual awareness
    con.execute("""
        CREATE TABLE IF NOT EXISTS awareness_edges (
            id VARCHAR PRIMARY KEY,
            source_session VARCHAR,
            target_session VARCHAR,
            edge_type VARCHAR,  -- 'play', 'coplay', 'fork', 'reference'
            strength DOUBLE DEFAULT 1.0,
            detected_via VARCHAR,
            trit INTEGER,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(source_session, target_session, edge_type)
        )
    """)
    
    # Temporal reflow index
    con.execute("""
        CREATE TABLE IF NOT EXISTS temporal_index (
            timestamp TIMESTAMP,
            message_id VARCHAR,
            session_id VARCHAR,
            trit INTEGER,
            epoch INTEGER
        )
    """)
    
    # GF(3) conservation ledger
    con.execute("""
        CREATE TABLE IF NOT EXISTS trit_ledger (
            epoch INTEGER PRIMARY KEY,
            plus_count INTEGER DEFAULT 0,
            ergodic_count INTEGER DEFAULT 0,
            minus_count INTEGER DEFAULT 0,
            sum_mod3 INTEGER DEFAULT 0,
            verified_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    """)
    
    # Create indexes
    con.execute("CREATE INDEX IF NOT EXISTS idx_msg_session ON messages(session_id)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_msg_ts ON messages(timestamp)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_msg_trit ON messages(trit)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_edge_src ON awareness_edges(source_session)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_edge_tgt ON awareness_edges(target_session)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_temporal ON temporal_index(timestamp, epoch)")
    print("✓ Schema created")

def find_jsonl_files() -> list[Path]:
    """Find all Claude .jsonl history files."""
    files = list(CLAUDE_PROJECTS.rglob("*.jsonl"))
    return files

def parse_jsonl_file(path: Path) -> Generator[Dict[str, Any], None, None]:
    """MINUS (-1): Validate and parse JSONL file."""
    try:
        with open(path, 'r', encoding='utf-8', errors='replace') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                    obj['_source_file'] = str(path)
                    obj['_line_num'] = line_num
                    obj['_trit'] = -1  # MINUS validated
                    yield obj
                except json.JSONDecodeError:
                    continue
    except Exception as e:
        print(f"  ⚠ Error reading {path}: {e}")

def transform_message(obj: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """ERGODIC (0): Transform and normalize message."""
    msg_type = obj.get('type')
    if msg_type in ('file-history-snapshot',):
        return None  # Skip snapshot updates
    
    uuid = obj.get('uuid') or obj.get('messageId')
    if not uuid:
        return None
    
    session_id = obj.get('sessionId', '')
    parent_uuid = obj.get('parentUuid')
    timestamp_str = obj.get('timestamp')
    
    # Parse timestamp
    timestamp = None
    if timestamp_str:
        try:
            timestamp = datetime.fromisoformat(timestamp_str.replace('Z', '+00:00'))
        except:
            pass
    
    # Extract content preview
    content = ''
    message = obj.get('message', {})
    if isinstance(message, dict):
        content_list = message.get('content', [])
        if isinstance(content_list, list) and content_list:
            first = content_list[0]
            if isinstance(first, dict):
                content = first.get('text', '')[:200]
            elif isinstance(first, str):
                content = first[:200]
        elif isinstance(content_list, str):
            content = content_list[:200]
        role = message.get('role', msg_type)
        model = message.get('model', '')
    else:
        role = msg_type
        model = ''
    
    # GF(3) trit from uuid
    trit = gf3_from_string(uuid)
    
    return {
        'id': uuid,
        'session_id': session_id,
        'parent_id': parent_uuid,
        'type': msg_type,
        'role': role,
        'timestamp': timestamp,
        'cwd': obj.get('cwd'),
        'git_branch': obj.get('gitBranch'),
        'agent_id': obj.get('agentId'),
        'model': model,
        'content_preview': content,
        'trit': trit,
        '_ergodic': 0  # ERGODIC transformed
    }

def insert_messages(con, messages: list[Dict[str, Any]], file_path: Path) -> Tuple[int, int, int]:
    """PLUS (+1): Insert transformed messages into DuckLake."""
    inserted = 0
    trit_counts = {-1: 0, 0: 0, 1: 0}
    
    for msg in messages:
        if not msg:
            continue
        try:
            con.execute("""
                INSERT OR REPLACE INTO messages 
                (id, session_id, parent_id, type, role, timestamp, cwd, git_branch, 
                 agent_id, model, content_preview, trit)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, [
                msg['id'], msg['session_id'], msg['parent_id'], msg['type'],
                msg['role'], msg['timestamp'], msg['cwd'], msg['git_branch'],
                msg['agent_id'], msg['model'], msg['content_preview'], msg['trit']
            ])
            inserted += 1
            trit_counts[msg['trit']] += 1
            
            # Insert into temporal index
            if msg['timestamp']:
                epoch = int(msg['timestamp'].timestamp() // 3600)  # Hourly epochs
                con.execute("""
                    INSERT OR IGNORE INTO temporal_index 
                    (timestamp, message_id, session_id, trit, epoch)
                    VALUES (?, ?, ?, ?, ?)
                """, [msg['timestamp'], msg['id'], msg['session_id'], msg['trit'], epoch])
                
        except Exception as e:
            pass
    
    # Update session stats
    session_ids = set(m['session_id'] for m in messages if m and m.get('session_id'))
    for sid in session_ids:
        project_path = str(file_path.parent).replace(str(CLAUDE_PROJECTS) + '/', '')
        try:
            con.execute("""
                INSERT INTO sessions (session_id, project_path, file_path, first_message_at, 
                                      last_message_at, message_count, trit)
                SELECT 
                    ?,
                    ?,
                    ?,
                    MIN(timestamp),
                    MAX(timestamp),
                    COUNT(*),
                    ?
                FROM messages WHERE session_id = ?
                ON CONFLICT(session_id) DO UPDATE SET
                    message_count = excluded.message_count,
                    last_message_at = excluded.last_message_at
            """, [sid, project_path, str(file_path), gf3_from_string(sid), sid])
        except:
            pass
    
    return trit_counts[-1], trit_counts[0], trit_counts[1]

def build_awareness_edges(con):
    """Build play/coplay edges from session temporal overlap and references."""
    print("\n⚡ Building mutual awareness graph...")
    
    # Fork edges: sessions from same project directory
    con.execute("""
        INSERT OR IGNORE INTO awareness_edges (id, source_session, target_session, edge_type, strength, detected_via, trit)
        SELECT 
            s1.session_id || ':fork:' || s2.session_id,
            s1.session_id,
            s2.session_id,
            'fork',
            1.0 / NULLIF(COUNT(*) OVER (PARTITION BY s1.project_path), 0),
            'same_project',
            0
        FROM sessions s1
        JOIN sessions s2 ON s1.project_path = s2.project_path 
            AND s1.session_id < s2.session_id
    """)
    
    # Temporal overlap edges (play): sessions active in same hour
    con.execute("""
        INSERT OR IGNORE INTO awareness_edges (id, source_session, target_session, edge_type, strength, detected_via, trit)
        SELECT 
            t1.session_id || ':play:' || t2.session_id,
            t1.session_id,
            t2.session_id,
            'play',
            1.0,
            'temporal_overlap',
            1
        FROM temporal_index t1
        JOIN temporal_index t2 ON t1.epoch = t2.epoch 
            AND t1.session_id < t2.session_id
        GROUP BY t1.session_id, t2.session_id
        HAVING COUNT(*) > 1
    """)
    
    # Coplay edges (bidirectional): inverse of play
    con.execute("""
        INSERT OR IGNORE INTO awareness_edges (id, source_session, target_session, edge_type, strength, detected_via, trit)
        SELECT 
            target_session || ':coplay:' || source_session,
            target_session,
            source_session,
            'coplay',
            strength,
            'inverse_play',
            -1
        FROM awareness_edges 
        WHERE edge_type = 'play'
    """)
    
    edge_count = con.execute("SELECT COUNT(*) FROM awareness_edges").fetchone()[0]
    print(f"  ✓ Created {edge_count} awareness edges")

def verify_gf3_conservation(con) -> bool:
    """Verify GF(3) conservation: Σ trits ≡ 0 (mod 3)."""
    result = con.execute("""
        SELECT 
            SUM(CASE WHEN trit = 1 THEN 1 ELSE 0 END) as plus,
            SUM(CASE WHEN trit = 0 THEN 1 ELSE 0 END) as ergodic,
            SUM(CASE WHEN trit = -1 THEN 1 ELSE 0 END) as minus,
            SUM(trit) as total,
            SUM(trit) % 3 as mod3
        FROM messages
    """).fetchone()
    
    plus, ergodic, minus, total, mod3 = result
    conserved = (total % 3) == 0 if total else True
    
    print(f"\n📊 GF(3) Verification:")
    print(f"  PLUS (+1):    {plus or 0}")
    print(f"  ERGODIC (0):  {ergodic or 0}")
    print(f"  MINUS (-1):   {minus or 0}")
    print(f"  Total: {total or 0}, mod 3 = {mod3 or 0}")
    print(f"  Conservation: {'✓ VERIFIED' if conserved else '✗ VIOLATION'}")
    
    return conserved

def main():
    print("╔════════════════════════════════════════════════════════════╗")
    print("║     CLAUDE COGNITION → DUCKLAKE INGESTION                  ║")
    print("║   MINUS (-1) → ERGODIC (0) → PLUS (+1) = 0 ✓               ║")
    print("╚════════════════════════════════════════════════════════════╝")
    
    # Ensure directory exists
    DUCKLAKE_PATH.parent.mkdir(parents=True, exist_ok=True)
    
    con = duckdb.connect(str(DUCKLAKE_PATH))
    create_schema(con)
    
    # Find all files
    files = find_jsonl_files()
    print(f"\n📁 Found {len(files)} .jsonl files in {CLAUDE_PROJECTS}")
    
    total_minus = total_ergodic = total_plus = 0
    files_processed = 0
    
    for i, file_path in enumerate(files):
        # MINUS: Parse
        raw_messages = list(parse_jsonl_file(file_path))
        
        # ERGODIC: Transform
        transformed = [transform_message(m) for m in raw_messages]
        transformed = [m for m in transformed if m]
        
        # PLUS: Insert
        if transformed:
            m, e, p = insert_messages(con, transformed, file_path)
            total_minus += m
            total_ergodic += e
            total_plus += p
            files_processed += 1
        
        if (i + 1) % 100 == 0:
            print(f"  ... processed {i + 1}/{len(files)} files")
    
    print(f"\n✓ Ingested {files_processed} files")
    print(f"  Trit distribution: -1={total_minus}, 0={total_ergodic}, +1={total_plus}")
    
    # Build awareness graph
    build_awareness_edges(con)
    
    # Verify conservation
    verify_gf3_conservation(con)
    
    # Summary stats
    msg_count = con.execute("SELECT COUNT(*) FROM messages").fetchone()[0]
    session_count = con.execute("SELECT COUNT(*) FROM sessions").fetchone()[0]
    edge_count = con.execute("SELECT COUNT(*) FROM awareness_edges").fetchone()[0]
    
    print(f"\n📈 DuckLake Stats:")
    print(f"  Messages:  {msg_count}")
    print(f"  Sessions:  {session_count}")
    print(f"  Edges:     {edge_count}")
    print(f"  DB Path:   {DUCKLAKE_PATH}")
    
    con.close()
    print("\n✓ Done!")

if __name__ == "__main__":
    main()
