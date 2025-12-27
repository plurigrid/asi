#!/usr/bin/env python3
"""
Thread Exchange Monitor - Real-time dashboard of P2P transfers
Shows thread searches, files exchanged, peer connectivity
"""

import os
import json
import time
from datetime import datetime
from pathlib import Path
from collections import defaultdict
import subprocess

class ThreadExchangeMonitor:
    def __init__(self):
        self.log_dir = Path("/tmp/thread_exchange_logs")
        self.result_dir = Path("/tmp")
        self.recv_dir = Path("/tmp/localsend_received")
        self.log_dir.mkdir(exist_ok=True)

    def get_recent_exchanges(self, limit=10):
        """Get recent exchange operations"""
        if not self.log_dir.exists():
            return []

        files = sorted(
            self.log_dir.glob("exchange_*.log"),
            key=lambda x: x.stat().st_mtime,
            reverse=True
        )[:limit]

        exchanges = []
        for f in files:
            try:
                with open(f) as fp:
                    content = fp.read()
                    # Extract info from log
                    timestamp = f.name.replace("exchange_", "").replace(".log", "")
                    sent_count = content.count("[✓] File sent")
                    exchanges.append({
                        "timestamp": timestamp,
                        "files_sent": sent_count,
                        "size": f.stat().st_size
                    })
            except:
                pass

        return exchanges

    def get_received_files(self):
        """Get list of received files"""
        if not self.recv_dir.exists():
            return []

        files = []
        try:
            for f in self.recv_dir.iterdir():
                if f.is_file():
                    files.append({
                        "name": f.name,
                        "size_mb": f.stat().st_size / (1024*1024),
                        "mtime": datetime.fromtimestamp(f.stat().st_mtime).isoformat()
                    })
        except:
            pass

        return sorted(files, key=lambda x: x['mtime'], reverse=True)

    def get_search_results(self):
        """Get recent search results"""
        results = []
        try:
            for f in self.result_dir.glob("thread_exchange_*.json"):
                with open(f) as fp:
                    data = json.load(fp)
                    # Extract summary
                    concept = f.name.replace("thread_exchange_", "").replace(".json", "")

                    if isinstance(data, list):
                        threads_searched = len(data)
                        files_sent = sum(r.get("files_sent_count", 0) for r in data if isinstance(r, dict))
                    else:
                        threads_searched = 1 if data else 0
                        files_sent = data.get("files_sent_count", 0) if data else 0

                    results.append({
                        "concept": concept,
                        "threads_searched": threads_searched,
                        "files_sent": files_sent,
                        "timestamp": datetime.fromtimestamp(f.stat().st_mtime).isoformat()
                    })
        except:
            pass

        return sorted(results, key=lambda x: x['timestamp'], reverse=True)

    def get_peer_status(self):
        """Check peer connectivity"""
        peers = []
        peer_ips = {
            "2-monad": "100.87.209.11",
            "causality": "100.69.33.107"
        }

        for name, ip in peer_ips.items():
            result = subprocess.run(
                ["ping", "-c", "1", "-W", "1000", ip],
                capture_output=True,
                text=True,
                timeout=3
            )

            is_online = result.returncode == 0

            peers.append({
                "name": name,
                "ip": ip,
                "online": is_online,
                "status": "🟢 ONLINE" if is_online else "🔴 OFFLINE"
            })

        return peers

    def get_stats(self):
        """Get aggregate statistics"""
        received_files = self.get_received_files()
        exchanges = self.get_recent_exchanges()
        search_results = self.get_search_results()

        total_received_gb = sum(f['size_mb'] for f in received_files) / 1024
        total_files_sent = sum(e['files_sent'] for e in exchanges)

        return {
            "total_files_received": len(received_files),
            "total_data_received_gb": round(total_received_gb, 2),
            "total_files_sent": total_files_sent,
            "total_searches": len(search_results),
            "exchanges_last_24h": len([e for e in exchanges])
        }

    def print_dashboard(self):
        """Print formatted dashboard"""
        print("\n" + "=" * 80)
        print("  THREAD EXCHANGE MONITOR - LIVE DASHBOARD")
        print("=" * 80)

        # Peer status
        print("\n[PEER CONNECTIVITY]")
        peers = self.get_peer_status()
        for p in peers:
            print(f"  {p['status']} {p['name']:15} {p['ip']}")

        # Stats
        print("\n[STATISTICS]")
        stats = self.get_stats()
        print(f"  Files Received:      {stats['total_files_received']:3}")
        print(f"  Data Received:       {stats['total_data_received_gb']:.2f} GB")
        print(f"  Files Sent:          {stats['total_files_sent']:3}")
        print(f"  Concept Searches:    {stats['total_searches']:3}")

        # Recent searches
        print("\n[RECENT SEARCHES] (top 5)")
        for result in self.get_search_results()[:5]:
            print(f"  • {result['concept']:15} threads={result['threads_searched']:2} "
                  f"sent={result['files_sent']:2} @ {result['timestamp']}")

        # Recent exchanges
        print("\n[RECENT EXCHANGES] (top 5)")
        for exchange in self.get_recent_exchanges()[:5]:
            print(f"  • {exchange['timestamp']:20} sent={exchange['files_sent']:2} files")

        # Received files
        print("\n[RECEIVED FILES] (top 10)")
        for f in self.get_received_files()[:10]:
            print(f"  • {f['name']:40} {f['size_mb']:8.2f} MB @ {f['mtime']}")

        print("\n" + "=" * 80)
        print(f"  Updated: {datetime.now().isoformat()}")
        print("=" * 80 + "\n")

    def watch(self, interval=5):
        """Continuously monitor with refresh"""
        try:
            while True:
                self.print_dashboard()
                time.sleep(interval)
        except KeyboardInterrupt:
            print("\n[Monitoring stopped]")

def main():
    import sys

    monitor = ThreadExchangeMonitor()

    if len(sys.argv) > 1 and sys.argv[1] == "watch":
        interval = int(sys.argv[2]) if len(sys.argv) > 2 else 5
        monitor.watch(interval)
    else:
        monitor.print_dashboard()

if __name__ == "__main__":
    main()
