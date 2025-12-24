#!/usr/bin/env python3
"""
Thread Search + LocalSend P2P Exchange
Finds relevant threads and exchanges files via localsend-mcp
"""

import json
import subprocess
import os
import re
from pathlib import Path
from typing import List, Dict, Tuple
import duckdb

# ============================================================================
# CONFIGURATION
# ============================================================================

THREAD_LAKE_DB = "/Users/bob/ies/music-topos/lib/unified_thread_lake.duckdb"
LOCALSEND_SKILL = "/Users/bob/.amp/skills/localsend-mcp"
LOCALSEND_RECEIVER_LOG = "/tmp/localsend_receiver.log"
LOCALSEND_SEND_SCRIPT = f"{LOCALSEND_SKILL}/localsend.bb"
DISCOVERY_SCRIPT = f"{LOCALSEND_SKILL}/discovery.bb"

# Self identity (from peers.edn)
SELF = {
    "name": "causality",
    "tailscale_ip": "100.69.33.107",
    "tailscale_dns": "causality.pirate-dragon.ts.net",
    "port": 53317
}

# Known peer (2-monad)
PEERS = {
    "2-monad": {
        "name": "2-monad",
        "tailscale_ip": "100.87.209.11",
        "tailscale_dns": "2-monad.pirate-dragon.ts.net",
        "port": 53317,
        "color": "#83D88F"
    }
}

# Thread concept index for mapping threads to file types
CONCEPT_FILE_MAP = {
    "skill": [".jl", ".py", ".rb", ".bb"],
    "MCP": [".json", ".py", ".bb"],
    "DuckDB": [".duckdb", ".sql", ".py"],
    "ACSet": [".jl", ".py", ".json"],
    "GF3": [".py", ".jl", ".bb"],
    "LocalSend": [".bb", ".py", ".edn"],
    "Babashka": [".bb", ".clj", ".edn"],
    "Clojure": [".clj", ".cljs", ".edn"],
    "HyJAX": [".py", ".jl", ".bb"],
    "alife": [".py", ".jl", ".json"],
    "topos": [".jl", ".py", ".rb", ".json"],
    "Synadia": [".py", ".bb", ".json"],
}

# ============================================================================
# THREAD SEARCH
# ============================================================================

def search_threads(query: str, limit: int = 5) -> List[Dict]:
    """Search unified thread lake by concept"""
    try:
        conn = duckdb.connect(THREAD_LAKE_DB, read_only=True)

        # Search for threads containing the concept
        sql = f"""
        SELECT DISTINCT
            thread_id,
            COUNT(*) as weight
        FROM concept_relations
        WHERE concept_from ILIKE '%{query}%'
           OR concept_to ILIKE '%{query}%'
        GROUP BY thread_id
        ORDER BY weight DESC
        LIMIT {limit}
        """

        result = conn.execute(sql).fetchall()
        conn.close()

        return [{"thread_id": r[0], "weight": r[1]} for r in result]
    except Exception as e:
        print(f"[ERROR] Thread search failed: {e}")
        return []

def get_thread_concepts(thread_id: str) -> List[str]:
    """Get all concepts for a thread"""
    try:
        conn = duckdb.connect(THREAD_LAKE_DB, read_only=True)
        sql = f"""
        SELECT DISTINCT concept
        FROM thread_concepts
        WHERE thread_id = '{thread_id}'
        """
        result = conn.execute(sql).fetchall()
        conn.close()
        return [r[0] for r in result]
    except Exception as e:
        print(f"[ERROR] Failed to get concepts: {e}")
        return []

# ============================================================================
# FILE DISCOVERY
# ============================================================================

def find_files_by_concepts(concepts: List[str], search_path: str = "/Users/bob/ies/music-topos") -> List[str]:
    """Find files matching thread concepts"""
    files = []
    file_extensions = set()

    # Gather all relevant extensions
    for concept in concepts:
        if concept in CONCEPT_FILE_MAP:
            file_extensions.update(CONCEPT_FILE_MAP[concept])

    if not file_extensions:
        return []

    # Search for files
    try:
        for root, dirs, filenames in os.walk(search_path):
            # Skip hidden and cache dirs
            dirs[:] = [d for d in dirs if not d.startswith('.') and d != '__pycache__']

            for filename in filenames:
                ext = Path(filename).suffix.lower()
                if ext in file_extensions:
                    full_path = os.path.join(root, filename)
                    files.append(full_path)
    except Exception as e:
        print(f"[ERROR] File discovery failed: {e}")

    return files[:10]  # Limit to 10 files per concept

# ============================================================================
# LOCALSEND INTEGRATION
# ============================================================================

def get_available_peers() -> List[Dict]:
    """Get list of available peers via discovery"""
    print("[PEER DISCOVERY]")
    print(f"  Known peer: 2-monad @ {PEERS['2-monad']['tailscale_ip']}:53317")
    return [PEERS["2-monad"]]

def start_localsend_receiver() -> bool:
    """Start LocalSend receiver if not running"""
    try:
        # Check if already running
        result = subprocess.run(["lsof", "-i", ":53317"], capture_output=True, text=True)
        if "localsend" in result.stdout or len(result.stdout) > 0:
            print("[✓] LocalSend receiver already running")
            return True

        # Start receiver in background
        print("[STARTING] LocalSend receiver on port 53317...")
        subprocess.Popen([
            "bb", LOCALSEND_SEND_SCRIPT, "receive"
        ], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

        import time
        time.sleep(2)
        print("[✓] Receiver started")
        return True
    except Exception as e:
        print(f"[ERROR] Failed to start receiver: {e}")
        return False

def announce_peer() -> bool:
    """Announce this peer's availability"""
    try:
        print("[ANNOUNCING] LocalSend peer availability...")
        subprocess.run([
            "say", "-v", "Emma (Premium)",
            f"LocalSend peer {SELF['name']} ready on port {SELF['port']}!"
        ], check=False)
        return True
    except Exception as e:
        print(f"[ERROR] Announcement failed: {e}")
        return False

def send_file_to_peer(file_path: str, peer_ip: str, peer_name: str = "2-monad") -> bool:
    """Send a file to a peer via LocalSend"""
    if not os.path.exists(file_path):
        print(f"[ERROR] File not found: {file_path}")
        return False

    try:
        file_size = os.path.getsize(file_path)
        filename = os.path.basename(file_path)

        print(f"[SENDING] {filename} ({file_size} bytes) to {peer_name}@{peer_ip}...")

        # Use LocalSend send script
        result = subprocess.run([
            "bb", LOCALSEND_SEND_SCRIPT, "send", file_path, peer_ip
        ], capture_output=True, text=True, timeout=30)

        if result.returncode == 0:
            print(f"[✓] File sent successfully")
            return True
        else:
            print(f"[ERROR] Send failed: {result.stderr}")
            return False
    except Exception as e:
        print(f"[ERROR] Send error: {e}")
        return False

# ============================================================================
# THREAD-BASED EXCHANGE ORCHESTRATION
# ============================================================================

def exchange_for_thread(thread_id: str, peer_name: str = "2-monad") -> Dict:
    """Complete exchange workflow for a thread"""
    print(f"\n{'='*70}")
    print(f"  THREAD EXCHANGE: {thread_id}")
    print(f"{'='*70}")

    result = {
        "thread_id": thread_id,
        "concepts": [],
        "files_found": [],
        "files_sent": [],
        "status": "pending"
    }

    # Step 1: Get concepts for this thread
    concepts = get_thread_concepts(thread_id)
    result["concepts"] = concepts
    print(f"\n[CONCEPTS] {', '.join(concepts)}")

    # Step 2: Find related files
    files = find_files_by_concepts(concepts)
    result["files_found"] = files
    print(f"\n[FILES FOUND] {len(files)} files")
    for f in files[:5]:
        size_mb = os.path.getsize(f) / (1024*1024)
        print(f"  • {os.path.basename(f)} ({size_mb:.2f} MB)")

    # Step 3: Get peer info
    peer_info = PEERS.get(peer_name)
    if not peer_info:
        result["status"] = "error_no_peer"
        print(f"\n[ERROR] Peer '{peer_name}' not found")
        return result

    peer_ip = peer_info["tailscale_ip"]

    # Step 4: Start receiver
    if not start_localsend_receiver():
        result["status"] = "error_receiver"
        return result

    # Step 5: Send files
    print(f"\n[TRANSFER] Sending to {peer_name} ({peer_ip})...")

    sent_count = 0
    for file_path in files[:3]:  # Limit to 3 files per thread
        if send_file_to_peer(file_path, peer_ip, peer_name):
            result["files_sent"].append(file_path)
            sent_count += 1

    result["status"] = "complete"
    result["files_sent_count"] = sent_count

    print(f"\n[RESULT] Sent {sent_count}/{len(files)} files")

    return result

def search_and_exchange(concept: str, peer_name: str = "2-monad") -> List[Dict]:
    """Search for threads matching concept and exchange files"""
    print(f"\n{'='*70}")
    print(f"  SEARCH & EXCHANGE: {concept}")
    print(f"{'='*70}\n")

    # Announce availability
    announce_peer()

    # Search threads
    threads = search_threads(concept)
    print(f"[SEARCH] Found {len(threads)} threads for '{concept}'")
    for t in threads:
        print(f"  • {t['thread_id'][:20]}... (weight: {t['weight']})")

    # Exchange for each thread
    results = []
    for thread_info in threads[:3]:  # Limit to top 3
        result = exchange_for_thread(thread_info["thread_id"], peer_name)
        results.append(result)

    return results

# ============================================================================
# MAIN CLI
# ============================================================================

def main():
    import sys

    print("\n" + "="*70)
    print("  THREAD SEARCH + LOCALSEND P2P EXCHANGE")
    print("="*70)

    if len(sys.argv) < 2:
        print("\nUsage:")
        print("  python3 thread_exchange.py search <concept>")
        print("  python3 thread_exchange.py exchange <thread_id>")
        print("  python3 thread_exchange.py discover")
        print("\nExamples:")
        print("  python3 thread_exchange.py search skill")
        print("  python3 thread_exchange.py search MCP")
        print("  python3 thread_exchange.py discover")
        return

    command = sys.argv[1]

    if command == "search":
        if len(sys.argv) < 3:
            print("[ERROR] Please provide a concept to search")
            return
        concept = sys.argv[2]
        results = search_and_exchange(concept)

        # Save results
        output_file = f"/tmp/thread_exchange_{concept}.json"
        with open(output_file, "w") as f:
            json.dump(results, f, indent=2)
        print(f"\n[SAVED] Results to {output_file}")

    elif command == "exchange":
        if len(sys.argv) < 3:
            print("[ERROR] Please provide a thread ID")
            return
        thread_id = sys.argv[2]
        result = exchange_for_thread(thread_id)

        output_file = f"/tmp/exchange_{thread_id[:8]}.json"
        with open(output_file, "w") as f:
            json.dump(result, f, indent=2)
        print(f"\n[SAVED] Results to {output_file}")

    elif command == "discover":
        peers = get_available_peers()
        print(f"\n[PEERS] {len(peers)} available")
        for p in peers:
            print(f"  • {p['name']} @ {p['tailscale_ip']}:53317")

        start_localsend_receiver()
        announce_peer()

    else:
        print(f"[ERROR] Unknown command: {command}")

if __name__ == "__main__":
    main()
