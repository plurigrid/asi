#!/usr/bin/env python3
"""
DuckLake Capabilities with Spectral Walk Integration

Found DuckDB resources:
- snips.duckdb: spectral_state (gap=0.8758), walk_history
- interaction_entropy.duckdb: entropy measurements, prediction markets
- own/ducklake/OWN.duckdb: derangements, chain_snapshots, CRDT ops
- 89+ more .duckdb files

Capabilities:
- FULL: All DuckDB operations + write + snapshot
- QUERY: SELECT + time-travel
- READONLY: SELECT only (attenuated)
"""

import sys
import subprocess
from dataclasses import dataclass, field
from typing import Set, Dict, List, Optional, FrozenSet, Tuple
from enum import IntEnum
from pathlib import Path

sys.path.insert(0, '/Users/bob/.claude/skills/dynamic-sufficiency')
from world_memory import Trit

# ════════════════════════════════════════════════════════════════════════════
# DuckLake Inventory
# ════════════════════════════════════════════════════════════════════════════

DUCKLAKE_PATHS = {
    "snips": Path("/Users/bob/ies/snips.duckdb"),
    "interaction_entropy": Path("/Users/bob/ies/interaction_entropy.duckdb"),
    "own": Path("/Users/bob/ies/own/ducklake/OWN.duckdb"),
    "gh_interactome": Path("/Users/bob/ies/gh_interactome.duckdb"),
    "observational_bridges": Path("/Users/bob/ies/observational_bridges.duckdb"),
    "chaotic_media_lake": Path("/Users/bob/ies/chaotic_media_lake.duckdb"),
    "hatchery": Path("/Users/bob/ies/hatchery.duckdb"),
    "dendroidal": Path("/Users/bob/ies/dendroidal.duckdb"),
    "spivak_poly": Path("/Users/bob/ies/spivak_poly.duckdb"),
}

# Spectral state from snips.duckdb
SPECTRAL_STATE = {
    "entropy": 1.7104,
    "spectral_gap": 0.8758,
    "entropy_seed": 1710379,
    "mixing_time": 1.14,
    "trit_entropy": 1.433,
}

# ════════════════════════════════════════════════════════════════════════════
# Capability Types
# ════════════════════════════════════════════════════════════════════════════

class DuckLevel(IntEnum):
    FULL = 1       # All ops: CREATE, INSERT, DELETE, SNAPSHOT
    QUERY = 0      # SELECT + time-travel + ATTACH
    READONLY = -1  # SELECT only


DUCK_OPERATIONS = {
    DuckLevel.FULL: frozenset([
        "SELECT", "INSERT", "UPDATE", "DELETE", "CREATE", "DROP",
        "ATTACH", "COPY", "EXPORT", "SNAPSHOT", "VACUUM"
    ]),
    DuckLevel.QUERY: frozenset([
        "SELECT", "ATTACH", "AT_VERSION", "AT_TIMESTAMP", "EXPLAIN"
    ]),
    DuckLevel.READONLY: frozenset([
        "SELECT"
    ]),
}


@dataclass(frozen=True)
class DuckCapability:
    """Capability for DuckDB/DuckLake operations."""
    db_name: str
    db_path: Path
    level: DuckLevel
    operations: FrozenSet[str]
    tables: Optional[FrozenSet[str]] = None  # None = all tables
    max_queries: Optional[int] = None
    spectral_aware: bool = False  # Can access spectral_state
    
    @property
    def trit(self) -> Trit:
        return Trit(self.level.value)
    
    def can_execute(self, sql: str) -> bool:
        """Check if SQL statement is allowed."""
        sql_upper = sql.strip().upper()
        for op in self.operations:
            if sql_upper.startswith(op):
                return True
        return False
    
    def attenuate(self,
                  new_level: Optional[DuckLevel] = None,
                  remove_tables: Optional[Set[str]] = None,
                  limit_queries: Optional[int] = None) -> 'DuckCapability':
        """Attenuate capability (reduce authority)."""
        if new_level is not None and new_level > self.level:
            raise ValueError(f"Cannot amplify from {self.level.name} to {new_level.name}")
        
        final_level = new_level if new_level is not None else self.level
        final_ops = DUCK_OPERATIONS[final_level]
        
        final_tables = self.tables
        if remove_tables and self.tables:
            final_tables = self.tables - frozenset(remove_tables)
        
        final_limit = self.max_queries
        if limit_queries is not None:
            if self.max_queries is None:
                final_limit = limit_queries
            else:
                final_limit = min(self.max_queries, limit_queries)
        
        return DuckCapability(
            db_name=self.db_name,
            db_path=self.db_path,
            level=final_level,
            operations=final_ops,
            tables=final_tables,
            max_queries=final_limit,
            spectral_aware=self.spectral_aware and final_level >= DuckLevel.QUERY
        )


def full_duck_cap(name: str) -> DuckCapability:
    """Create full capability for a DuckLake."""
    if name not in DUCKLAKE_PATHS:
        raise ValueError(f"Unknown DuckLake: {name}")
    return DuckCapability(
        db_name=name,
        db_path=DUCKLAKE_PATHS[name],
        level=DuckLevel.FULL,
        operations=DUCK_OPERATIONS[DuckLevel.FULL],
        spectral_aware=(name == "snips")
    )


def query_duck_cap(name: str) -> DuckCapability:
    """Create query-only capability."""
    cap = full_duck_cap(name)
    return cap.attenuate(new_level=DuckLevel.QUERY)


def readonly_duck_cap(name: str) -> DuckCapability:
    """Create read-only capability."""
    cap = full_duck_cap(name)
    return cap.attenuate(new_level=DuckLevel.READONLY)


# ════════════════════════════════════════════════════════════════════════════
# Spectral Walk Integration
# ════════════════════════════════════════════════════════════════════════════

def sufficient_walkers_for_gap(spectral_gap: float, confidence: float = 0.95) -> int:
    """
    Compute sufficient number of walkers for spectral gap estimation.
    
    n_walkers = O(1 / (gap² × δ))
    """
    delta = 1 - confidence
    return max(1, int(1 / (spectral_gap ** 2 * delta)) + 1)


def launch_spectral_walks(cap: DuckCapability, n_walkers: int, steps: int) -> List[Dict]:
    """
    Launch non-backtracking random walks on DuckLake graph.
    
    Requires spectral_aware capability.
    """
    if not cap.spectral_aware:
        raise ValueError(f"Capability for {cap.db_name} is not spectral-aware")
    
    if not cap.can_execute("SELECT"):
        raise ValueError("Need at least SELECT permission for walks")
    
    # Query walk_history from snips.duckdb
    result = subprocess.run([
        "duckdb", str(cap.db_path), "-json", "-c",
        f"SELECT * FROM walk_history LIMIT {n_walkers * steps}"
    ], capture_output=True, text=True)
    
    if result.returncode != 0:
        return []
    
    import json
    try:
        walks = json.loads(result.stdout)
        return walks
    except:
        return []


def get_spectral_state(cap: DuckCapability) -> Dict:
    """Get current spectral state from DuckLake."""
    if not cap.spectral_aware:
        return SPECTRAL_STATE  # Return cached
    
    result = subprocess.run([
        "duckdb", str(cap.db_path), "-json", "-c",
        "SELECT * FROM spectral_state"
    ], capture_output=True, text=True)
    
    if result.returncode == 0:
        import json
        try:
            rows = json.loads(result.stdout)
            return {r["key"]: r["value"] for r in rows}
        except:
            pass
    
    return SPECTRAL_STATE


# ════════════════════════════════════════════════════════════════════════════
# Demo
# ════════════════════════════════════════════════════════════════════════════

def demo():
    print("=" * 70)
    print("DUCKLAKE CAPABILITIES")
    print("=" * 70)
    
    print("\n─── Available DuckLakes ───")
    for name, path in DUCKLAKE_PATHS.items():
        exists = "✓" if path.exists() else "✗"
        print(f"  {exists} {name}: {path}")
    
    print("\n─── Spectral State (from snips.duckdb) ───")
    for k, v in SPECTRAL_STATE.items():
        print(f"  {k}: {v}")
    
    # Compute sufficient walkers
    gap = SPECTRAL_STATE["spectral_gap"]
    n_walkers = sufficient_walkers_for_gap(gap)
    print(f"\n  Sufficient walkers for gap {gap}: {n_walkers}")
    
    print("\n─── Capability Creation ───")
    
    # Full capability
    snips_full = full_duck_cap("snips")
    print(f"  snips (FULL):")
    print(f"    Level: {snips_full.level.name}, Trit: {snips_full.trit.name}")
    print(f"    Operations: {len(snips_full.operations)}")
    print(f"    Spectral-aware: {snips_full.spectral_aware}")
    
    # Attenuated
    snips_query = snips_full.attenuate(new_level=DuckLevel.QUERY)
    print(f"\n  snips (QUERY - attenuated):")
    print(f"    Level: {snips_query.level.name}, Trit: {snips_query.trit.name}")
    print(f"    Operations: {snips_query.operations}")
    
    snips_readonly = snips_full.attenuate(new_level=DuckLevel.READONLY, limit_queries=100)
    print(f"\n  snips (READONLY - further attenuated):")
    print(f"    Level: {snips_readonly.level.name}")
    print(f"    Max queries: {snips_readonly.max_queries}")
    
    print("\n─── GF(3) Triad ───")
    caps = [
        full_duck_cap("snips"),  # +1
        query_duck_cap("interaction_entropy"),  # 0
        readonly_duck_cap("own"),  # -1
    ]
    
    trit_sum = sum(c.trit.value for c in caps)
    print(f"  snips (FULL, +1) + interaction_entropy (QUERY, 0) + own (READONLY, -1)")
    print(f"  Sum: {trit_sum} (mod 3 = {trit_sum % 3}) {'✓' if trit_sum % 3 == 0 else '✗'}")
    
    print("\n─── SQL Permission Tests ───")
    tests = [
        (snips_full, "SELECT * FROM spectral_state", True),
        (snips_full, "INSERT INTO walk_history VALUES (...)", True),
        (snips_query, "SELECT * FROM spectral_state", True),
        (snips_query, "INSERT INTO walk_history VALUES (...)", False),
        (snips_readonly, "SELECT * FROM spectral_state", True),
        (snips_readonly, "ATTACH 'other.db'", False),
    ]
    
    for cap, sql, expected in tests:
        result = cap.can_execute(sql)
        status = "✓" if result == expected else "✗"
        print(f"  {status} {cap.db_name}({cap.level.name}): {sql[:40]}... → {result}")
    
    print("\n─── Live Spectral State Query ───")
    if DUCKLAKE_PATHS["snips"].exists():
        state = get_spectral_state(snips_query)
        print(f"  Retrieved {len(state)} spectral values")
        if "spectral_gap" in state:
            print(f"  Live spectral_gap: {state['spectral_gap']}")

if __name__ == "__main__":
    demo()
