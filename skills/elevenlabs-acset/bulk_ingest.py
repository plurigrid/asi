#!/usr/bin/env python3
"""
Bulk Ingest - Lazy/Bulk download of all interaction data for media company pipeline.

Sources:
- SoundCloud (rickroderick)
- Bandcamp (monaduck69)  
- poe.com/bmorphism
- ElevenLabs API history
- Signal backup
- DuckDB sources
- Hatchery repos

Output: ~/.topos/interactions.duckdb
"""

import os
import json
import asyncio
from pathlib import Path
from datetime import datetime
from typing import Iterator, Optional
import duckdb

# Paths
TOPOS_HOME = Path.home() / ".topos"
DB_PATH = TOPOS_HOME / "interactions.duckdb"
SIGNAL_BACKUP = Path.home() / "ies" / "signal_backup_20251230_185106"
HATCHERY_REPOS = Path.home() / "ies" / "hatchery_repos"

# =============================================================================
# LAZY ITERATORS
# =============================================================================

def lazy_signal_messages(backup_path: Path) -> Iterator[dict]:
    """Lazily iterate through Signal messages."""
    export_file = backup_path / "signal_maximal_export.json"
    if not export_file.exists():
        return
    
    # Stream JSON for memory efficiency
    with open(export_file, 'r') as f:
        data = json.load(f)
    
    for conversation in data.get("conversations", []):
        for msg in conversation.get("messages", []):
            yield {
                "source": "signal",
                "conversation_id": conversation.get("id", ""),
                "timestamp": msg.get("timestamp", ""),
                "body": msg.get("body", ""),
                "sender": msg.get("sender", ""),
                "type": msg.get("type", "message")
            }


def lazy_hatchery_gay_md(hatchery_path: Path) -> Iterator[dict]:
    """Lazily iterate through GAY.md files in hatchery repos."""
    if not hatchery_path.exists():
        return
    
    for gay_md in hatchery_path.rglob("GAY.md"):
        repo_name = gay_md.parent.name
        content = gay_md.read_text()
        
        # Extract color from GAY.md
        color = None
        seed = None
        for line in content.split('\n'):
            if 'Repo Color:' in line:
                color = line.split('`')[1] if '`' in line else None
            if 'Seed:' in line:
                seed = line.split('`')[1] if '`' in line else None
        
        yield {
            "source": "hatchery",
            "repo_name": repo_name,
            "color": color,
            "seed": seed,
            "path": str(gay_md)
        }


def lazy_duckdb_sources(topos_home: Path) -> Iterator[dict]:
    """Lazily discover all DuckDB files."""
    for db_file in topos_home.rglob("*.duckdb"):
        try:
            conn = duckdb.connect(str(db_file), read_only=True)
            tables = conn.execute("SHOW TABLES").fetchall()
            conn.close()
            
            yield {
                "source": "duckdb",
                "path": str(db_file),
                "tables": [t[0] for t in tables],
                "size_bytes": db_file.stat().st_size
            }
        except Exception as e:
            yield {
                "source": "duckdb",
                "path": str(db_file),
                "error": str(e)
            }


def lazy_ducklake_sources(topos_home: Path) -> Iterator[dict]:
    """Lazily discover all DuckLake files."""
    for lake_file in topos_home.rglob("*.ducklake"):
        yield {
            "source": "ducklake",
            "path": str(lake_file),
            "size_bytes": lake_file.stat().st_size
        }


# =============================================================================
# BULK DOWNLOAD
# =============================================================================

async def fetch_soundcloud_tracks(username: str = "rickroderick") -> list[dict]:
    """Fetch SoundCloud track metadata (requires API or scraping)."""
    # Placeholder - would need SoundCloud API key or scraping
    return [{
        "source": "soundcloud",
        "username": username,
        "url": f"https://soundcloud.com/{username}",
        "status": "api_key_required",
        "known_tracks": [
            "axioms",
            "r-o-d-e-r-i-c-k-w-a-v-e",
            "roderickwhale"
        ]
    }]


async def fetch_bandcamp_releases(username: str = "monaduck69") -> list[dict]:
    """Fetch Bandcamp release metadata."""
    return [{
        "source": "bandcamp",
        "username": username,
        "url": f"https://{username}.bandcamp.com",
        "status": "scrape_available"
    }]


async def fetch_elevenlabs_history() -> list[dict]:
    """Fetch ElevenLabs generation history."""
    api_key = os.getenv("ELEVENLABS_API_KEY")
    if not api_key:
        return [{"source": "elevenlabs", "status": "api_key_missing"}]
    
    try:
        import httpx
        async with httpx.AsyncClient() as client:
            resp = await client.get(
                "https://api.elevenlabs.io/v1/history",
                headers={"xi-api-key": api_key}
            )
            if resp.status_code == 200:
                data = resp.json()
                return [{
                    "source": "elevenlabs",
                    "history_items": len(data.get("history", [])),
                    "status": "success"
                }]
            else:
                return [{"source": "elevenlabs", "status": f"error_{resp.status_code}"}]
    except Exception as e:
        return [{"source": "elevenlabs", "status": f"error: {e}"}]


# =============================================================================
# DUCKDB SCHEMA
# =============================================================================

def init_interactions_db(db_path: Path) -> duckdb.DuckDBPyConnection:
    """Initialize interactions database with schema."""
    conn = duckdb.connect(str(db_path))
    
    conn.execute("""
        CREATE SEQUENCE IF NOT EXISTS seq_interactions START 1;
        CREATE SEQUENCE IF NOT EXISTS seq_sources START 1;
        CREATE SEQUENCE IF NOT EXISTS seq_hatchery START 1;
        CREATE SEQUENCE IF NOT EXISTS seq_duckdb START 1;
    """)
    
    conn.execute("""
        CREATE TABLE IF NOT EXISTS interactions (
            id INTEGER DEFAULT nextval('seq_interactions') PRIMARY KEY,
            source VARCHAR NOT NULL,
            source_id VARCHAR,
            timestamp TIMESTAMP,
            content TEXT,
            metadata JSON,
            trit INTEGER DEFAULT 0,
            color VARCHAR,
            created_at TIMESTAMP DEFAULT now()
        )
    """)
    
    conn.execute("""
        CREATE TABLE IF NOT EXISTS sources (
            id INTEGER DEFAULT nextval('seq_sources') PRIMARY KEY,
            name VARCHAR UNIQUE NOT NULL,
            type VARCHAR,
            url VARCHAR,
            last_sync TIMESTAMP,
            item_count INTEGER DEFAULT 0,
            metadata JSON
        )
    """)
    
    conn.execute("""
        CREATE TABLE IF NOT EXISTS hatchery_repos (
            id INTEGER DEFAULT nextval('seq_hatchery') PRIMARY KEY,
            repo_name VARCHAR UNIQUE NOT NULL,
            gay_color VARCHAR,
            gay_seed VARCHAR,
            path VARCHAR,
            synced_at TIMESTAMP DEFAULT now()
        )
    """)
    
    conn.execute("""
        CREATE TABLE IF NOT EXISTS duckdb_inventory (
            id INTEGER DEFAULT nextval('seq_duckdb') PRIMARY KEY,
            path VARCHAR UNIQUE NOT NULL,
            tables JSON,
            size_bytes BIGINT,
            discovered_at TIMESTAMP DEFAULT now()
        )
    """)
    
    return conn


def bulk_ingest_all(lazy: bool = True):
    """
    Bulk ingest all interaction data.
    
    Args:
        lazy: If True, use lazy iterators for memory efficiency.
              If False, load everything into memory first.
    """
    print(f"🦆 Initializing interactions database at {DB_PATH}")
    conn = init_interactions_db(DB_PATH)
    
    # Register sources
    sources = [
        ("soundcloud", "audio", "https://soundcloud.com/rickroderick"),
        ("bandcamp", "audio", "https://monaduck69.bandcamp.com"),
        ("poe", "chatbot", "https://poe.com/bmorphism"),
        ("elevenlabs", "voice_api", "https://api.elevenlabs.io"),
        ("signal", "messaging", "+14156960069"),
        ("hatchery", "repos", str(HATCHERY_REPOS)),
    ]
    
    for name, stype, url in sources:
        now = datetime.now().isoformat()
        conn.execute("""
            INSERT INTO sources (name, type, url, last_sync)
            VALUES (?, ?, ?, ?)
            ON CONFLICT (name) DO UPDATE SET
                type = EXCLUDED.type,
                url = EXCLUDED.url,
                last_sync = EXCLUDED.last_sync
        """, (name, stype, url, now))
    
    # Ingest Signal messages (lazy)
    print("📱 Ingesting Signal messages...")
    signal_count = 0
    for msg in lazy_signal_messages(SIGNAL_BACKUP):
        if msg.get("body"):
            conn.execute("""
                INSERT INTO interactions (source, source_id, timestamp, content, metadata)
                VALUES (?, ?, ?, ?, ?)
            """, ("signal", msg["conversation_id"], msg["timestamp"], 
                  msg["body"], json.dumps(msg)))
            signal_count += 1
        if signal_count % 10000 == 0:
            print(f"  ... {signal_count} messages")
    print(f"  ✓ {signal_count} Signal messages ingested")
    
    # Ingest Hatchery GAY.md files
    print("🌈 Ingesting Hatchery GAY.md files...")
    hatchery_count = 0
    for repo in lazy_hatchery_gay_md(HATCHERY_REPOS):
        conn.execute("""
            INSERT INTO hatchery_repos (repo_name, gay_color, gay_seed, path)
            VALUES (?, ?, ?, ?)
            ON CONFLICT DO NOTHING
        """, (repo["repo_name"], repo.get("color"), repo.get("seed"), repo["path"]))
        hatchery_count += 1
    print(f"  ✓ {hatchery_count} repos with GAY.md")
    
    # Discover DuckDB sources
    print("🗄️ Discovering DuckDB sources...")
    duckdb_count = 0
    for source in lazy_duckdb_sources(TOPOS_HOME):
        if "error" not in source:
            conn.execute("""
                INSERT INTO duckdb_inventory (path, tables, size_bytes)
                VALUES (?, ?, ?)
                ON CONFLICT DO NOTHING
            """, (source["path"], json.dumps(source.get("tables", [])), 
                  source.get("size_bytes", 0)))
            duckdb_count += 1
    
    # Also scan ~/ies for DuckDB files
    ies_path = Path.home() / "ies"
    for source in lazy_duckdb_sources(ies_path):
        if "error" not in source:
            conn.execute("""
                INSERT INTO duckdb_inventory (path, tables, size_bytes)
                VALUES (?, ?, ?)
                ON CONFLICT DO NOTHING
            """, (source["path"], json.dumps(source.get("tables", [])),
                  source.get("size_bytes", 0)))
            duckdb_count += 1
    print(f"  ✓ {duckdb_count} DuckDB files discovered")
    
    # Update source counts
    conn.execute("""
        UPDATE sources SET item_count = (
            SELECT COUNT(*) FROM interactions WHERE source = sources.name
        )
    """)
    
    conn.close()
    print(f"\n✅ Bulk ingest complete: {DB_PATH}")
    print(f"   Signal: {signal_count} | Hatchery: {hatchery_count} | DuckDB: {duckdb_count}")


async def async_bulk_fetch():
    """Async fetch from external APIs."""
    print("🌐 Fetching external sources...")
    
    results = await asyncio.gather(
        fetch_soundcloud_tracks(),
        fetch_bandcamp_releases(),
        fetch_elevenlabs_history(),
        return_exceptions=True
    )
    
    for r in results:
        if isinstance(r, Exception):
            print(f"  ⚠ Error: {r}")
        else:
            for item in r:
                print(f"  ✓ {item.get('source')}: {item.get('status', 'ok')}")


# =============================================================================
# CLI
# =============================================================================

if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1 and sys.argv[1] == "--async":
        print("Running async bulk fetch...")
        asyncio.run(async_bulk_fetch())
    else:
        print("Running bulk ingest (lazy mode)...")
        bulk_ingest_all(lazy=True)
