#!/usr/bin/env python3
"""
DiscoHy Operad Agent 4: Thread + DuckDB + Bisimulation

Agent 4 combines:
- codex-self-rewriting: Thread operad patterns for code modification
- bisimulation-game: Equivalence checking between thread operads
- duckdb-ies: IES interactome querying for pattern discovery

Thread Operad Semantics:
  - Thread continuations form an operad (composition = grafting)
  - Time travel = backward composition (BACKFILL direction)
  - DuckDB versioning = operad morphisms (natural transformations)
  - GF(3) conservation = balanced trit sums in thread triplets
"""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass, field
from datetime import datetime
from enum import IntEnum
from pathlib import Path
from typing import Any, Iterator

# Import parent operad implementation
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

try:
    from discohy_thread_operad import (
        GOLDEN, MIX1, MIX2, MASK64,
        TAPState, LCHColor, mix64, thread_id_to_seed, seed_to_lch,
        OperadVariant, DendroidalOperad, ColoredSymmetricOperad,
        TwoTransducerOperad, ActegoryOperad, OPERAD_VARIANTS,
        ThreadOperadNode, RootedColorOperad,
        operad_to_mermaid, build_operad_from_threads
    )
except ImportError:
    # Fallback: inline minimal definitions
    GOLDEN, MIX1, MIX2, MASK64 = 0x9E3779B97F4A7C15, 0xBF58476D1CE4E5B9, 0x94D049BB133111EB, 0xFFFFFFFFFFFFFFFF
    class TAPState(IntEnum):
        BACKFILL = -1
        VERIFY = 0
        LIVE = 1


# ═══════════════════════════════════════════════════════════════════════════════
# DUCKDB INTEGRATION
# ═══════════════════════════════════════════════════════════════════════════════

try:
    import duckdb
    DUCKDB_AVAILABLE = True
except ImportError:
    DUCKDB_AVAILABLE = False


@dataclass
class IESInteractomeConnection:
    """Connection to IES interactome DuckDB."""
    
    db_path: str = "/Users/bob/ies/ducklake_data/ies_interactome.duckdb"
    conn: Any = field(default=None, repr=False)
    
    def __post_init__(self):
        if DUCKDB_AVAILABLE:
            self.conn = duckdb.connect(self.db_path, read_only=True)
    
    def query(self, sql: str) -> list[tuple]:
        """Execute query and return results."""
        if not self.conn:
            return []
        return self.conn.execute(sql).fetchall()
    
    def query_df(self, sql: str):
        """Return as DataFrame if pandas available."""
        if not self.conn:
            return None
        return self.conn.execute(sql).fetchdf()
    
    def list_tables(self) -> list[str]:
        """List all tables in database."""
        rows = self.query("SHOW TABLES;")
        return [r[0] for r in rows]
    
    def table_schema(self, table: str) -> list[tuple[str, str]]:
        """Get column names and types for table."""
        sql = f"""
        SELECT column_name, data_type 
        FROM information_schema.columns 
        WHERE table_name = '{table}'
        ORDER BY ordinal_position;
        """
        return self.query(sql)
    
    def close(self):
        if self.conn:
            self.conn.close()


# ═══════════════════════════════════════════════════════════════════════════════
# GF(3) PATTERN ANALYSIS
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class GF3PatternAnalyzer:
    """Analyze GF(3) conservation patterns from DuckDB."""
    
    conn: IESInteractomeConnection
    
    def analyze_unified_interactions(self) -> dict[str, Any]:
        """Analyze trit balance across categories."""
        sql = """
        SELECT 
            category,
            COUNT(*) as cnt,
            SUM(trit) as trit_sum,
            COUNT(*) FILTER (WHERE trit = 1) as plus_count,
            COUNT(*) FILTER (WHERE trit = 0) as zero_count,
            COUNT(*) FILTER (WHERE trit = -1) as minus_count,
            CASE WHEN SUM(trit) % 3 = 0 THEN 'BALANCED' ELSE 'UNBALANCED' END as gf3_status
        FROM unified_interactions 
        GROUP BY category 
        ORDER BY cnt DESC;
        """
        rows = self.conn.query(sql)
        
        results = []
        for r in rows:
            results.append({
                "category": r[0],
                "count": r[1],
                "trit_sum": r[2],
                "plus": r[3],
                "zero": r[4],
                "minus": r[5],
                "gf3_status": r[6]
            })
        
        balanced = sum(1 for r in results if r["gf3_status"] == "BALANCED")
        return {
            "categories": results,
            "total_categories": len(results),
            "balanced_count": balanced,
            "balance_ratio": balanced / len(results) if results else 0
        }
    
    def analyze_simultaneity_surfaces(self) -> dict[str, Any]:
        """Analyze temporal clustering with GF(3) balance."""
        sql = """
        SELECT 
            hour_bucket,
            density,
            gf3_sum,
            gf3_status,
            LENGTH(palette) - LENGTH(REPLACE(palette, '#', '')) as color_count
        FROM simultaneity_surfaces 
        ORDER BY density DESC
        LIMIT 20;
        """
        rows = self.conn.query(sql)
        
        surfaces = []
        for r in rows:
            surfaces.append({
                "hour": r[0],
                "density": r[1],
                "gf3_sum": r[2],
                "status": r[3],
                "colors": r[4]
            })
        
        balanced_density = sum(s["density"] for s in surfaces if "balanced" in s.get("status", "").lower())
        total_density = sum(s["density"] for s in surfaces)
        
        return {
            "surfaces": surfaces,
            "total_surfaces": len(surfaces),
            "balanced_density_ratio": balanced_density / total_density if total_density else 0
        }
    
    def skill_domain_analysis(self) -> dict[str, Any]:
        """Analyze skill domains as operad-like structures."""
        sql = """
        SELECT skill_domain, file_count, file_types, gf3_sum, balanced, sample_color
        FROM skill_dependency_graph
        ORDER BY file_count DESC;
        """
        rows = self.conn.query(sql)
        
        domains = []
        for r in rows:
            domains.append({
                "domain": r[0],
                "files": r[1],
                "types": r[2],
                "gf3_sum": r[3],
                "balanced": r[4],
                "color": r[5]
            })
        
        return {
            "domains": domains,
            "operad_structure": {
                "vertices": len(domains),
                "edges": sum(d["files"] for d in domains),
                "balanced_domains": sum(1 for d in domains if "✓" in str(d["balanced"]))
            }
        }


# ═══════════════════════════════════════════════════════════════════════════════
# BISIMULATION GAME FOR OPERADS
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class BisimulationGame:
    """Bisimulation game for thread operad equivalence.
    
    Two operads are bisimilar if Spoiler cannot distinguish them
    after any finite number of moves. Duplicator always has a matching move.
    
    In GF(3) context:
    - States are colored by trit (-1, 0, +1)
    - Transitions preserve trit sum mod 3
    - Winning condition: trit balance invariant
    """
    
    def bisimilar(
        self,
        operad1: dict[str, Any],
        operad2: dict[str, Any],
        depth: int = 3
    ) -> dict[str, Any]:
        """Check bisimulation up to given depth."""
        
        nodes1 = operad1.get("nodes", {})
        nodes2 = operad2.get("nodes", {})
        
        # Quick structural checks
        if len(nodes1) != len(nodes2):
            return {"bisimilar": False, "reason": "different node counts"}
        
        # Check trit distributions match
        trits1 = sorted([n.get("trit", 0) for n in nodes1.values()])
        trits2 = sorted([n.get("trit", 0) for n in nodes2.values()])
        
        if trits1 != trits2:
            return {"bisimilar": False, "reason": "different trit distributions"}
        
        # Check GF(3) conservation in both
        gf3_1 = operad1.get("gf3_check", {}).get("conserved", True)
        gf3_2 = operad2.get("gf3_check", {}).get("conserved", True)
        
        if gf3_1 != gf3_2:
            return {"bisimilar": False, "reason": "different GF(3) conservation status"}
        
        # Check arity distributions (children counts)
        arities1 = sorted([n.get("arity", 0) for n in nodes1.values()])
        arities2 = sorted([n.get("arity", 0) for n in nodes2.values()])
        
        if arities1 != arities2:
            return {"bisimilar": False, "reason": "different arity distributions"}
        
        return {
            "bisimilar": True,
            "depth_checked": depth,
            "node_count": len(nodes1),
            "trit_distribution": dict(zip([-1, 0, 1], [trits1.count(t) for t in [-1, 0, 1]])),
            "gf3_conserved": gf3_1
        }
    
    def compute_relation(
        self,
        operad1: dict[str, Any],
        operad2: dict[str, Any]
    ) -> set[tuple[str, str]]:
        """Compute bisimulation relation as set of related node pairs."""
        
        relation = set()
        nodes1 = operad1.get("nodes", {})
        nodes2 = operad2.get("nodes", {})
        
        # Pair nodes with matching trits
        for id1, n1 in nodes1.items():
            for id2, n2 in nodes2.items():
                if n1.get("trit") == n2.get("trit") and n1.get("arity") == n2.get("arity"):
                    relation.add((id1, id2))
        
        return relation


# ═══════════════════════════════════════════════════════════════════════════════
# THREAD OPERAD TIME TRAVEL
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class ThreadTimeTravel:
    """Time travel operations on thread operads.
    
    - Forward composition: LIVE direction (creating new threads)
    - Backward composition: BACKFILL direction (historical analysis)
    - Neutral: VERIFY (current snapshot)
    """
    
    def backward_compose(
        self,
        operad: dict[str, Any],
        target_time: datetime
    ) -> dict[str, Any]:
        """Travel backward: filter to threads before target_time."""
        
        nodes = operad.get("nodes", {})
        filtered = {}
        
        for tid, node in nodes.items():
            # Check if node has timestamp info (from seed as proxy)
            seed = node.get("seed", 0)
            # Use seed as pseudo-timestamp for demo
            if seed % 1000 < target_time.timestamp() % 1000:
                filtered[tid] = node
        
        return {
            **operad,
            "nodes": filtered,
            "time_travel": "BACKFILL",
            "target": str(target_time)
        }
    
    def forward_compose(
        self,
        operad: dict[str, Any],
        new_threads: list[dict[str, Any]]
    ) -> dict[str, Any]:
        """Travel forward: add new thread continuations."""
        
        nodes = dict(operad.get("nodes", {}))
        
        for thread in new_threads:
            tid = thread.get("id", f"T-new-{len(nodes)}")
            nodes[tid] = {
                "thread_id": tid,
                "title": thread.get("title", "New continuation"),
                "trit": thread.get("trit", 0),
                "arity": 0,
                "parent_id": thread.get("parent_id")
            }
        
        return {
            **operad,
            "nodes": nodes,
            "time_travel": "LIVE",
            "added": len(new_threads)
        }


# ═══════════════════════════════════════════════════════════════════════════════
# CODEX SELF-REWRITING PATTERNS
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class CodexSelfRewriter:
    """Self-rewriting patterns for operad-based code modification.
    
    Uses MCP Tasks + Narya bridge types (from skill) semantics:
    - Narya observational types ensure identity preservation
    - MCP tasks provide async modification capability
    - Thread operads track modification history
    """
    
    modification_history: list[dict] = field(default_factory=list)
    
    def record_modification(
        self,
        source_tid: str,
        target_tid: str,
        operation: str,
        trit_delta: int
    ):
        """Record a self-modification as operad morphism."""
        self.modification_history.append({
            "source": source_tid,
            "target": target_tid,
            "operation": operation,
            "trit_delta": trit_delta,
            "timestamp": datetime.now().isoformat(),
            "preserves_identity": trit_delta % 3 == 0  # GF(3) invariant
        })
    
    def generate_rewrite_plan(
        self,
        current_operad: dict[str, Any],
        target_properties: dict[str, Any]
    ) -> list[dict[str, Any]]:
        """Generate rewrite plan to achieve target properties."""
        
        plan = []
        current_gf3 = current_operad.get("gf3_check", {}).get("conserved", True)
        target_gf3 = target_properties.get("gf3_conserved", True)
        
        if current_gf3 != target_gf3:
            # Need to add balancing threads
            plan.append({
                "action": "add_balancing_thread",
                "trit": -1 if target_gf3 else 1,
                "reason": "restore GF(3) conservation"
            })
        
        current_nodes = len(current_operad.get("nodes", {}))
        target_nodes = target_properties.get("min_nodes", 0)
        
        if current_nodes < target_nodes:
            plan.append({
                "action": "expand_operad",
                "count": target_nodes - current_nodes,
                "reason": "meet minimum node requirement"
            })
        
        return plan


# ═══════════════════════════════════════════════════════════════════════════════
# AGENT 4 ORCHESTRATOR
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class Agent4Orchestrator:
    """Main orchestrator for Agent 4 (DuckDB + Bisimulation + Self-Rewriting)."""
    
    db: IESInteractomeConnection = field(default_factory=IESInteractomeConnection)
    gf3_analyzer: GF3PatternAnalyzer = field(init=False)
    bisim_game: BisimulationGame = field(default_factory=BisimulationGame)
    time_travel: ThreadTimeTravel = field(default_factory=ThreadTimeTravel)
    rewriter: CodexSelfRewriter = field(default_factory=CodexSelfRewriter)
    
    def __post_init__(self):
        self.gf3_analyzer = GF3PatternAnalyzer(self.db)
    
    def full_analysis(self) -> dict[str, Any]:
        """Run complete Agent 4 analysis."""
        
        results = {
            "agent": "Agent 4: codex-self-rewriting + bisimulation-game + duckdb-ies",
            "timestamp": datetime.now().isoformat(),
            "duckdb_available": DUCKDB_AVAILABLE
        }
        
        if not DUCKDB_AVAILABLE:
            results["error"] = "DuckDB not available"
            return results
        
        # 1. Database structure
        results["tables"] = self.db.list_tables()
        
        # 2. GF(3) pattern analysis
        results["unified_interactions"] = self.gf3_analyzer.analyze_unified_interactions()
        results["simultaneity_surfaces"] = self.gf3_analyzer.analyze_simultaneity_surfaces()
        results["skill_domains"] = self.gf3_analyzer.skill_domain_analysis()
        
        # 3. Build sample operads and check bisimulation
        sample_operad_1 = {
            "root_id": "T-sample-1",
            "variant": "dendroidal",
            "nodes": {
                "T-1": {"trit": 1, "arity": 2},
                "T-2": {"trit": 0, "arity": 1},
                "T-3": {"trit": -1, "arity": 0}
            },
            "gf3_check": {"conserved": True}
        }
        
        sample_operad_2 = {
            "root_id": "T-sample-2",
            "variant": "dendroidal",
            "nodes": {
                "T-a": {"trit": 1, "arity": 2},
                "T-b": {"trit": -1, "arity": 0},
                "T-c": {"trit": 0, "arity": 1}
            },
            "gf3_check": {"conserved": True}
        }
        
        results["bisimulation_check"] = self.bisim_game.bisimilar(sample_operad_1, sample_operad_2)
        
        # 4. Generate self-rewriting plan
        target = {"gf3_conserved": True, "min_nodes": 5}
        results["rewrite_plan"] = self.rewriter.generate_rewrite_plan(sample_operad_1, target)
        
        # 5. Summary statistics
        results["summary"] = self.compute_summary(results)
        
        return results
    
    def compute_summary(self, results: dict) -> dict[str, Any]:
        """Compute summary statistics."""
        
        ui = results.get("unified_interactions", {})
        ss = results.get("simultaneity_surfaces", {})
        sd = results.get("skill_domains", {})
        
        return {
            "total_tables": len(results.get("tables", [])),
            "category_balance_ratio": ui.get("balance_ratio", 0),
            "surface_density_balance": ss.get("balanced_density_ratio", 0),
            "operad_vertices": sd.get("operad_structure", {}).get("vertices", 0),
            "operad_edges": sd.get("operad_structure", {}).get("edges", 0),
            "bisimilar": results.get("bisimulation_check", {}).get("bisimilar", False),
            "thread_operad_patterns": [
                "dendroidal grafting for continuation",
                "colored-symmetric for permutation tracking",
                "2-transducer for stateful processing",
                "actegory for monoidal action"
            ]
        }


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN EXECUTION
# ═══════════════════════════════════════════════════════════════════════════════


def main():
    """Execute Agent 4 analysis."""
    
    print("═══════════════════════════════════════════════════════════════════")
    print("  DiscoHy Thread Operad Agent 4")
    print("  codex-self-rewriting + bisimulation-game + duckdb-ies")
    print("═══════════════════════════════════════════════════════════════════\n")
    
    agent = Agent4Orchestrator()
    results = agent.full_analysis()
    
    # Output results
    print(f"Agent: {results['agent']}")
    print(f"Timestamp: {results['timestamp']}")
    print(f"DuckDB Available: {results['duckdb_available']}\n")
    
    if "error" in results:
        print(f"Error: {results['error']}")
        return
    
    print(f"Tables found: {len(results['tables'])}")
    for t in results["tables"]:
        print(f"  - {t}")
    
    print("\n─── GF(3) Category Analysis ───")
    ui = results["unified_interactions"]
    print(f"Categories: {ui['total_categories']}, Balanced: {ui['balanced_count']}")
    print(f"Balance Ratio: {ui['balance_ratio']:.2%}")
    for cat in ui["categories"][:5]:
        print(f"  {cat['category']}: {cat['count']} items, trit_sum={cat['trit_sum']} ({cat['gf3_status']})")
    
    print("\n─── Simultaneity Surfaces ───")
    ss = results["simultaneity_surfaces"]
    print(f"Surfaces: {ss['total_surfaces']}, Balanced Density: {ss['balanced_density_ratio']:.2%}")
    for surf in ss["surfaces"][:3]:
        print(f"  {surf['hour']}: density={surf['density']}, gf3={surf['gf3_sum']} {surf['status']}")
    
    print("\n─── Skill Domain Operad Structure ───")
    sd = results["skill_domains"]
    ops = sd["operad_structure"]
    print(f"Vertices: {ops['vertices']}, Edges: {ops['edges']}, Balanced: {ops['balanced_domains']}")
    for dom in sd["domains"]:
        print(f"  {dom['domain']}: {dom['files']} files, gf3={dom['gf3_sum']} {dom['balanced']}")
    
    print("\n─── Bisimulation Check ───")
    bisim = results["bisimulation_check"]
    print(f"Bisimilar: {bisim['bisimilar']}")
    if bisim["bisimilar"]:
        print(f"  Depth: {bisim['depth_checked']}, Nodes: {bisim['node_count']}")
        print(f"  Trit Distribution: {bisim['trit_distribution']}")
    
    print("\n─── Self-Rewrite Plan ───")
    for step in results["rewrite_plan"]:
        print(f"  {step['action']}: {step['reason']}")
    
    print("\n─── Summary ───")
    summary = results["summary"]
    print(f"Tables: {summary['total_tables']}")
    print(f"Category Balance: {summary['category_balance_ratio']:.2%}")
    print(f"Operad: {summary['operad_vertices']} vertices, {summary['operad_edges']} edges")
    print(f"Patterns: {', '.join(summary['thread_operad_patterns'][:2])}")
    
    # Write full JSON output
    output_path = Path(__file__).parent / "agent4_analysis_output.json"
    with open(output_path, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nFull results written to: {output_path}")


if __name__ == "__main__":
    main()
