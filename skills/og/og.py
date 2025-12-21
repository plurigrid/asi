#!/usr/bin/env python3
"""
og - Observational Bridge Time Travel Skill

Maintains plurigrid fork while cherry-picking from og (original) remote.
Tracks interactions in DuckDB buffers for crdt.el sexp state and Gay.jl colors.
"""

import os
import json
import time
import hashlib
import subprocess
import urllib.request
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from datetime import datetime

# DuckDB import (optional, graceful fallback)
try:
    import duckdb
    HAS_DUCKDB = True
except ImportError:
    HAS_DUCKDB = False

# Gay.jl SplitMix64 PRNG (matches exactly)
class SplitMix64:
    GOLDEN = 0x9E3779B97F4A7C15
    MIX1 = 0xBF58476D1CE4E5B9
    MIX2 = 0x94D049BB133111EB

    def __init__(self, seed: int):
        self.state = seed & 0xFFFFFFFFFFFFFFFF

    def next_u64(self) -> int:
        self.state = (self.state + self.GOLDEN) & 0xFFFFFFFFFFFFFFFF
        z = self.state
        z = ((z ^ (z >> 30)) * self.MIX1) & 0xFFFFFFFFFFFFFFFF
        z = ((z ^ (z >> 27)) * self.MIX2) & 0xFFFFFFFFFFFFFFFF
        return z ^ (z >> 31)

    def next_float(self) -> float:
        return self.next_u64() / 0xFFFFFFFFFFFFFFFF

class DrandBeacon:
    """League of Entropy drand beacon"""
    QUICKNET = "https://api.drand.sh/52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971"

    @classmethod
    def fetch(cls, round_num: Optional[int] = None) -> Dict[str, Any]:
        url = f"{cls.QUICKNET}/public/{'latest' if not round_num else round_num}"
        try:
            with urllib.request.urlopen(url, timeout=5) as resp:
                data = json.loads(resp.read())
                return {
                    "round": data["round"],
                    "seed": int(data["randomness"][:16], 16),
                    "randomness": data["randomness"]
                }
        except Exception as e:
            return {"round": 0, "seed": 1069, "randomness": "", "error": str(e)}

class GayColor:
    """Gay.jl color generation"""

    @staticmethod
    def color_at(seed: int, index: int) -> Dict[str, Any]:
        rng = SplitMix64(seed)
        for _ in range(index):
            rng.next_u64()

        L = 10 + rng.next_float() * 85
        C = rng.next_float() * 100
        H = rng.next_float() * 360

        # Girard polarity
        if H < 60:
            polarity = "positive"
        elif H < 120:
            polarity = "additive"
        elif H < 180:
            polarity = "neutral"
        elif H < 240:
            polarity = "negative"
        elif H < 300:
            polarity = "multiplicative"
        else:
            polarity = "positive"

        return {"L": L, "C": C, "H": H, "index": index, "girard_polarity": polarity}

    @staticmethod
    def lch_to_hex(lch: Dict[str, float]) -> str:
        import math
        L, C, H = lch["L"], lch["C"], lch["H"]
        h_rad = math.radians(H)
        a = C * math.cos(h_rad)
        b = C * math.sin(h_rad)

        r = int(max(0, min(255, L * 2.55 + a * 1.5)))
        g = int(max(0, min(255, L * 2.55 - a * 0.5 - b * 0.5)))
        b_val = int(max(0, min(255, L * 2.55 + b * 1.5)))

        return f"#{r:02X}{g:02X}{b_val:02X}"

class OGTimeTravelBuffer:
    """DuckDB buffer for time travel operations"""

    def __init__(self, db_path: str = "~/.og/time_travel.duckdb"):
        self.db_path = Path(db_path).expanduser()
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = None

        if HAS_DUCKDB:
            self.conn = duckdb.connect(str(self.db_path))
            self._init_schema()

    def _init_schema(self):
        if not self.conn:
            return

        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS cherry_pick_history (
                id INTEGER PRIMARY KEY,
                timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                commit_sha VARCHAR,
                source_remote VARCHAR,
                target_branch VARCHAR,
                decision INTEGER,  -- -1: reject, 0: defer (BEAVER), +1: accept
                color_hex VARCHAR,
                girard_polarity VARCHAR,
                moebius_mu INTEGER,
                drand_round INTEGER,
                drand_seed BIGINT
            )
        """)

        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS crdt_sexp_buffer (
                id INTEGER PRIMARY KEY,
                timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                session_id VARCHAR,
                sexp_content TEXT,
                operation VARCHAR,  -- 'insert', 'delete', 'modify'
                position_start INTEGER,
                position_end INTEGER,
                color_hex VARCHAR,
                girard_polarity VARCHAR
            )
        """)

        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS gay_color_invocations (
                id INTEGER PRIMARY KEY,
                timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                seed BIGINT,
                index_val INTEGER,
                hex_color VARCHAR,
                L DOUBLE,
                C DOUBLE,
                H DOUBLE,
                girard_polarity VARCHAR,
                source VARCHAR  -- 'cherry_pick', 'crdt_el', 'gay_mcp', 'rewrite'
            )
        """)

        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS gay_mcp_rewrites (
                id INTEGER PRIMARY KEY,
                timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                before_seed BIGINT,
                after_seed BIGINT,
                rewrite_type VARCHAR,  -- 'seed_mutation', 'palette_change', 'triangle_fail'
                affected_indices TEXT,  -- JSON array of indices
                drand_round INTEGER
            )
        """)

    def record_cherry_pick(self, commit_sha: str, decision: int, seed: int, index: int,
                          drand_round: int = 0, source_remote: str = "og",
                          target_branch: str = "asi-skillz") -> Dict[str, Any]:
        color = GayColor.color_at(seed, index)
        hex_color = GayColor.lch_to_hex(color)

        # Möbius mu calculation (simplified)
        moebius_mu = 1 if decision == 0 else ((-1) ** abs(decision))

        if self.conn:
            self.conn.execute("""
                INSERT INTO cherry_pick_history
                (commit_sha, source_remote, target_branch, decision, color_hex,
                 girard_polarity, moebius_mu, drand_round, drand_seed)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, [commit_sha, source_remote, target_branch, decision, hex_color,
                  color["girard_polarity"], moebius_mu, drand_round, seed])

            self._record_color_invocation(seed, index, color, hex_color, "cherry_pick")

        return {
            "commit_sha": commit_sha,
            "decision": decision,
            "decision_name": {-1: "reject", 0: "BEAVER", 1: "accept"}.get(decision),
            "color": hex_color,
            "girard_polarity": color["girard_polarity"],
            "moebius_mu": moebius_mu,
            "drand_round": drand_round
        }

    def record_crdt_sexp(self, session_id: str, sexp: str, operation: str,
                        pos_start: int, pos_end: int, seed: int, index: int):
        color = GayColor.color_at(seed, index)
        hex_color = GayColor.lch_to_hex(color)

        if self.conn:
            self.conn.execute("""
                INSERT INTO crdt_sexp_buffer
                (session_id, sexp_content, operation, position_start, position_end,
                 color_hex, girard_polarity)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, [session_id, sexp, operation, pos_start, pos_end,
                  hex_color, color["girard_polarity"]])

            self._record_color_invocation(seed, index, color, hex_color, "crdt_el")

    def record_gay_mcp_rewrite(self, before_seed: int, after_seed: int,
                               rewrite_type: str, affected_indices: List[int],
                               drand_round: int = 0):
        if self.conn:
            self.conn.execute("""
                INSERT INTO gay_mcp_rewrites
                (before_seed, after_seed, rewrite_type, affected_indices, drand_round)
                VALUES (?, ?, ?, ?, ?)
            """, [before_seed, after_seed, rewrite_type,
                  json.dumps(affected_indices), drand_round])

            # Record colors for before and after seeds
            for idx in affected_indices[:5]:  # Limit to first 5
                before_color = GayColor.color_at(before_seed, idx)
                after_color = GayColor.color_at(after_seed, idx)
                self._record_color_invocation(before_seed, idx, before_color,
                                             GayColor.lch_to_hex(before_color), "rewrite")
                self._record_color_invocation(after_seed, idx, after_color,
                                             GayColor.lch_to_hex(after_color), "rewrite")

    def _record_color_invocation(self, seed: int, index: int, color: Dict,
                                 hex_color: str, source: str):
        if self.conn:
            self.conn.execute("""
                INSERT INTO gay_color_invocations
                (seed, index_val, hex_color, L, C, H, girard_polarity, source)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """, [seed, index, hex_color, color["L"], color["C"], color["H"],
                  color["girard_polarity"], source])

    def time_travel_to_round(self, target_round: int) -> List[Dict]:
        """Get all operations that happened at/after a drand round"""
        if not self.conn:
            return []

        result = self.conn.execute("""
            SELECT * FROM cherry_pick_history
            WHERE drand_round >= ?
            ORDER BY drand_round, timestamp
        """, [target_round]).fetchall()

        return [dict(zip(["id", "timestamp", "commit_sha", "source_remote",
                         "target_branch", "decision", "color_hex", "girard_polarity",
                         "moebius_mu", "drand_round", "drand_seed"], row))
                for row in result]

    def get_sexp_buffer_state(self, session_id: str) -> List[Dict]:
        """Get crdt.el sexp buffer state for a session"""
        if not self.conn:
            return []

        result = self.conn.execute("""
            SELECT * FROM crdt_sexp_buffer
            WHERE session_id = ?
            ORDER BY timestamp
        """, [session_id]).fetchall()

        return [dict(zip(["id", "timestamp", "session_id", "sexp_content",
                         "operation", "position_start", "position_end",
                         "color_hex", "girard_polarity"], row))
                for row in result]

    def close(self):
        if self.conn:
            self.conn.close()

class OGSkill:
    """Main og skill implementation"""

    def __init__(self, repo_path: str = "."):
        self.repo_path = Path(repo_path)
        self.buffer = OGTimeTravelBuffer()
        self.current_seed = 1069
        self.operation_index = 0
        self.drand_round = 0

    def seed_from_drand(self, round_num: Optional[int] = None) -> Dict:
        beacon = DrandBeacon.fetch(round_num)
        self.current_seed = beacon["seed"]
        self.drand_round = beacon["round"]
        self.operation_index = 0
        return beacon

    def fetch_og(self) -> Dict[str, Any]:
        """Fetch from og remote with color tracking"""
        try:
            result = subprocess.run(
                ["git", "fetch", "og"],
                cwd=self.repo_path,
                capture_output=True,
                text=True
            )

            color = GayColor.color_at(self.current_seed, self.operation_index)
            hex_color = GayColor.lch_to_hex(color)
            self.operation_index += 1

            return {
                "success": result.returncode == 0,
                "color": hex_color,
                "girard_polarity": color["girard_polarity"],
                "stdout": result.stdout,
                "stderr": result.stderr
            }
        except Exception as e:
            return {"success": False, "error": str(e)}

    def cherry_pick(self, commit_sha: str, decision: Optional[int] = None) -> Dict[str, Any]:
        """Cherry-pick with balanced ternary decision tracking

        decision: -1 (reject), 0 (BEAVER/defer), +1 (accept)
        If decision is None, perform actual cherry-pick
        """
        if decision is None:
            # Actually try to cherry-pick
            try:
                result = subprocess.run(
                    ["git", "cherry-pick", commit_sha],
                    cwd=self.repo_path,
                    capture_output=True,
                    text=True
                )
                decision = 1 if result.returncode == 0 else -1
            except Exception:
                decision = -1

        record = self.buffer.record_cherry_pick(
            commit_sha=commit_sha,
            decision=decision,
            seed=self.current_seed,
            index=self.operation_index,
            drand_round=self.drand_round,
            source_remote="og",
            target_branch="asi-skillz"
        )

        self.operation_index += 1
        return record

    def record_crdt_interaction(self, session_id: str, sexp: str,
                                operation: str, pos_start: int, pos_end: int):
        """Record a crdt.el sexp interaction"""
        self.buffer.record_crdt_sexp(
            session_id=session_id,
            sexp=sexp,
            operation=operation,
            pos_start=pos_start,
            pos_end=pos_end,
            seed=self.current_seed,
            index=self.operation_index
        )
        self.operation_index += 1

    def record_gay_mcp_self_rewrite(self, new_seed: int,
                                    affected_indices: List[int],
                                    rewrite_type: str = "seed_mutation"):
        """Record GayMCP rewriting itself"""
        self.buffer.record_gay_mcp_rewrite(
            before_seed=self.current_seed,
            after_seed=new_seed,
            rewrite_type=rewrite_type,
            affected_indices=affected_indices,
            drand_round=self.drand_round
        )

        # The rewrite changes our seed (inside-out transformation)
        self.current_seed = new_seed
        self.operation_index = 0  # Reset index for new seed

    def time_travel(self, to_round: int) -> List[Dict]:
        """Time travel to a specific drand round"""
        return self.buffer.time_travel_to_round(to_round)

    def get_status(self) -> Dict[str, Any]:
        """Get current og skill status"""
        return {
            "current_seed": self.current_seed,
            "seed_hex": f"0x{self.current_seed:016X}",
            "operation_index": self.operation_index,
            "drand_round": self.drand_round,
            "repo_path": str(self.repo_path),
            "current_color": GayColor.lch_to_hex(
                GayColor.color_at(self.current_seed, self.operation_index)
            )
        }

    def close(self):
        self.buffer.close()

def main():
    """CLI interface for og skill"""
    import argparse

    parser = argparse.ArgumentParser(description="og - Observational Bridge Time Travel Skill")
    parser.add_argument("command", choices=["fetch", "cherry-pick", "time-travel", "status", "seed"])
    parser.add_argument("--sha", help="Commit SHA for cherry-pick")
    parser.add_argument("--decision", type=int, choices=[-1, 0, 1], help="Cherry-pick decision")
    parser.add_argument("--round", type=int, help="drand round for time-travel or seeding")
    parser.add_argument("--repo", default=".", help="Repository path")

    args = parser.parse_args()

    skill = OGSkill(repo_path=args.repo)

    try:
        if args.command == "status":
            print(json.dumps(skill.get_status(), indent=2))

        elif args.command == "seed":
            result = skill.seed_from_drand(args.round)
            print(json.dumps(result, indent=2))

        elif args.command == "fetch":
            result = skill.fetch_og()
            print(json.dumps(result, indent=2))

        elif args.command == "cherry-pick":
            if not args.sha:
                print("Error: --sha required for cherry-pick")
                return 1
            result = skill.cherry_pick(args.sha, args.decision)
            print(json.dumps(result, indent=2))

        elif args.command == "time-travel":
            if args.round is None:
                print("Error: --round required for time-travel")
                return 1
            results = skill.time_travel(args.round)
            print(json.dumps(results, indent=2, default=str))

    finally:
        skill.close()

    return 0

if __name__ == "__main__":
    exit(main())
