#!/usr/bin/env python3
"""
Harmonization Engine for gh-skill-explorer.

Like DuckLake creates snapshots on INSERT, we create conceptual snapshots
on each discovery/evolution event.

Usage:
    uv run harmonize.py snapshot --domain active-inference
    uv run harmonize.py dissonance --a discopy --b hott
    uv run harmonize.py evolve --from-snapshot 1 --concept "cups-as-paths"
"""
# /// script
# requires-python = ">=3.11"
# dependencies = ["duckdb", "pydantic", "rich"]
# ///

import json
from datetime import datetime
from pathlib import Path
from typing import Optional
from dataclasses import dataclass, field, asdict

import duckdb
from pydantic import BaseModel
from rich.console import Console
from rich.table import Table

console = Console()

# Domain profiles extracted from DeepWiki queries
# Shared axioms enable harmonization discovery
DOMAIN_PROFILES = {
    "discopy": {
        "repo": "discopy/discopy",
        "axioms": {"monoidal", "composition", "functor", "rigid", "symmetric", "categorical", "diagram"},
        "terms": {"cup", "cap", "box", "diagram", "tensor", "morphism"},
        "compose": "sequential+parallel",
        "goal": "categorical-semantics",
        "deepwiki": True,
    },
    "hott": {
        "repo": "HoTT/Coq-HoTT",
        "axioms": {"univalence", "path", "equivalence", "transport", "funext", "categorical", "functor"},
        "terms": {"path", "equiv", "homotopy", "fibration", "truncation", "morphism"},
        "compose": "path-concatenation",
        "goal": "foundational-equality",
        "deepwiki": True,
    },
    "cerebrum": {
        "repo": "ActiveInferenceInstitute/CEREBRUM",
        "axioms": {"free-energy", "bayesian", "case-system", "predictive", "flow", "dynamics"},
        "terms": {"case", "nominative", "accusative", "belief", "precision"},
        "compose": "case-transition",
        "goal": "minimize-surprise",
        "deepwiki": True,
    },
    "gflownet": {
        "repo": "zdhNarsil/Awesome-GFlowNets",
        "axioms": {"flow-matching", "proportional-sampling", "dag", "terminal", "flow", "dynamics"},
        "terms": {"flow", "trajectory", "reward", "backward", "forward"},
        "compose": "trajectory-building",
        "goal": "sample-proportionally",
        "deepwiki": True,
    },
    "particle-life": {
        "repo": "hunar4321/particle-life",
        "axioms": {"force-based", "interaction-matrix", "emergence", "viscosity", "dynamics"},
        "terms": {"particle", "attraction", "repulsion", "radius", "color"},
        "compose": "physics-update",
        "goal": "emergent-patterns",
        "deepwiki": True,
    },
    "composio": {
        "repo": "ComposioHQ/composio",
        "axioms": {"tool-router", "mcp", "oauth-cascade", "discovery", "composition"},
        "terms": {"toolkit", "session", "connected-account", "workbench"},
        "compose": "discovery-auth-execute",
        "goal": "tool-orchestration",
        "deepwiki": True,
    },
    "graphcast": {
        "repo": "google-deepmind/graphcast",
        "axioms": {"gnn", "mesh", "grid2mesh", "icosahedral", "transformer", "composition", "diagram"},
        "terms": {"mesh", "grid", "edge", "node", "refinement", "morphism"},
        "compose": "encoder-processor-decoder",
        "goal": "weather-prediction",
        "deepwiki": True,
    },
    "petri": {
        "repo": "AlgebraicJulia/Petri.jl",
        "axioms": {"acset", "dpo-rewriting", "stoichiometry", "categorical", "composition", "flow"},
        "terms": {"place", "transition", "token", "species", "reaction", "morphism"},
        "compose": "operad-composition",
        "goal": "reaction-network-modeling",
        "deepwiki": False,
    },
    "poly": {
        "repo": "ToposInstitute/poly",
        "axioms": {"polynomial-functor", "lens", "container", "dependent", "categorical", "functor"},
        "terms": {"position", "direction", "arena", "morphism", "map"},
        "compose": "polynomial-composition",
        "goal": "dynamic-systems",
        "deepwiki": False,
    },
}


def jaccard(set_a: set, set_b: set) -> float:
    """Jaccard similarity coefficient."""
    if not set_a and not set_b:
        return 1.0
    intersection = len(set_a & set_b)
    union = len(set_a | set_b)
    return intersection / union if union > 0 else 0.0


def compute_dissonance(domain_a: str, domain_b: str) -> dict:
    """
    Compute conceptual dissonance between two domains.
    
    Returns dict with:
    - score: 0.0 (consonant) to 1.0 (dissonant)
    - axiom_overlap: shared foundational concepts
    - vocab_overlap: shared terminology
    - compose_match: whether composition models align
    - goal_match: whether objectives align
    """
    prof_a = DOMAIN_PROFILES.get(domain_a)
    prof_b = DOMAIN_PROFILES.get(domain_b)
    
    if not prof_a or not prof_b:
        return {"error": f"Unknown domain(s): {domain_a}, {domain_b}"}
    
    axiom_similarity = jaccard(prof_a["axioms"], prof_b["axioms"])
    vocab_similarity = jaccard(prof_a["terms"], prof_b["terms"])
    compose_match = 1.0 if prof_a["compose"] == prof_b["compose"] else 0.0
    goal_match = 1.0 if prof_a["goal"] == prof_b["goal"] else 0.0
    
    # Weighted dissonance score (higher = more dissonant)
    dissonance = (
        (1.0 - axiom_similarity) * 0.3 +
        (1.0 - vocab_similarity) * 0.3 +
        (1.0 - compose_match) * 0.2 +
        (1.0 - goal_match) * 0.2
    )
    
    return {
        "domain_a": domain_a,
        "domain_b": domain_b,
        "dissonance_score": round(dissonance, 3),
        "axiom_overlap": list(prof_a["axioms"] & prof_b["axioms"]),
        "vocab_overlap": list(prof_a["terms"] & prof_b["terms"]),
        "compose_match": compose_match == 1.0,
        "goal_match": goal_match == 1.0,
        "rating": "HIGH" if dissonance > 0.7 else "MEDIUM" if dissonance > 0.4 else "LOW",
    }


@dataclass
class ConceptualSnapshot:
    """DuckLake-style snapshot for conceptual evolution."""
    
    version: int
    timestamp: str = field(default_factory=lambda: datetime.now().isoformat())
    domains_queried: list[str] = field(default_factory=list)
    dissonances: dict[str, float] = field(default_factory=dict)
    harmonizations: list[str] = field(default_factory=list)
    new_concepts: list[str] = field(default_factory=list)
    
    def record_dissonance(self, domain_a: str, domain_b: str, 
                          score: float, resolution: Optional[str] = None):
        """Record a conceptual tension between domains."""
        key = f"{domain_a}↔{domain_b}"
        self.dissonances[key] = score
        if resolution:
            self.harmonizations.append(f"{key}: {resolution}")
    
    def evolve(self, new_concept: str) -> 'ConceptualSnapshot':
        """Create new snapshot with evolved concept (DuckLake INSERT pattern)."""
        return ConceptualSnapshot(
            version=self.version + 1,
            domains_queried=self.domains_queried.copy(),
            dissonances=self.dissonances.copy(),
            harmonizations=self.harmonizations.copy(),
            new_concepts=[new_concept],
        )
    
    def to_dict(self) -> dict:
        return asdict(self)


class HarmonizationDB:
    """DuckDB-backed storage for conceptual snapshots."""
    
    def __init__(self, db_path: str = "harmonization.duckdb"):
        self.db = duckdb.connect(db_path)
        self._init_schema()
    
    def _init_schema(self):
        self.db.execute("""
            CREATE TABLE IF NOT EXISTS snapshots (
                version INTEGER PRIMARY KEY,
                timestamp TIMESTAMP,
                data JSON
            )
        """)
        self.db.execute("""
            CREATE TABLE IF NOT EXISTS dissonances (
                domain_a VARCHAR,
                domain_b VARCHAR,
                score FLOAT,
                rating VARCHAR,
                axiom_overlap JSON,
                computed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (domain_a, domain_b)
            )
        """)
    
    def save_snapshot(self, snapshot: ConceptualSnapshot):
        self.db.execute(
            "INSERT OR REPLACE INTO snapshots VALUES (?, ?, ?)",
            [snapshot.version, snapshot.timestamp, json.dumps(snapshot.to_dict())]
        )
    
    def get_latest_snapshot(self) -> Optional[ConceptualSnapshot]:
        result = self.db.execute(
            "SELECT data FROM snapshots ORDER BY version DESC LIMIT 1"
        ).fetchone()
        if result:
            data = json.loads(result[0])
            return ConceptualSnapshot(**data)
        return None
    
    def save_dissonance(self, result: dict):
        self.db.execute("""
            INSERT OR REPLACE INTO dissonances 
            (domain_a, domain_b, score, rating, axiom_overlap)
            VALUES (?, ?, ?, ?, ?)
        """, [
            result["domain_a"], 
            result["domain_b"], 
            result["dissonance_score"],
            result["rating"],
            json.dumps(result["axiom_overlap"]),
        ])
    
    def get_all_dissonances(self) -> list[dict]:
        result = self.db.execute(
            "SELECT * FROM dissonances ORDER BY score DESC"
        ).fetchall()
        return [
            {"domain_a": r[0], "domain_b": r[1], "score": r[2], "rating": r[3]}
            for r in result
        ]


def display_dissonance_matrix():
    """Display all pairwise dissonances as a matrix."""
    domains = list(DOMAIN_PROFILES.keys())
    
    table = Table(title="🎭 Dissonance Matrix")
    table.add_column("", style="bold")
    for d in domains:
        table.add_column(d[:8], style="cyan")
    
    for domain_a in domains:
        row = [domain_a[:8]]
        for domain_b in domains:
            if domain_a == domain_b:
                row.append("—")
            else:
                result = compute_dissonance(domain_a, domain_b)
                score = result["dissonance_score"]
                color = "red" if score > 0.7 else "yellow" if score > 0.4 else "green"
                row.append(f"[{color}]{score:.2f}[/{color}]")
        table.add_row(*row)
    
    console.print(table)


def display_domain_profile(domain: str):
    """Display detailed profile for a domain."""
    profile = DOMAIN_PROFILES.get(domain)
    if not profile:
        console.print(f"[red]Unknown domain: {domain}[/red]")
        return
    
    table = Table(title=f"📚 Domain Profile: {domain}")
    table.add_column("Property", style="bold")
    table.add_column("Value")
    
    table.add_row("Repository", profile["repo"])
    table.add_row("Axioms", ", ".join(sorted(profile["axioms"])))
    table.add_row("Terms", ", ".join(sorted(profile["terms"])))
    table.add_row("Composition", profile["compose"])
    table.add_row("Goal", profile["goal"])
    table.add_row("DeepWiki", "✅" if profile["deepwiki"] else "❌")
    
    console.print(table)


def find_harmonization_opportunities():
    """Find domains with shared axioms that could be bridged."""
    domains = list(DOMAIN_PROFILES.keys())
    opportunities = []
    
    for i, domain_a in enumerate(domains):
        for domain_b in domains[i+1:]:
            result = compute_dissonance(domain_a, domain_b)
            if result["axiom_overlap"]:
                opportunities.append({
                    "domains": (domain_a, domain_b),
                    "shared_axioms": result["axiom_overlap"],
                    "dissonance": result["dissonance_score"],
                })
    
    opportunities.sort(key=lambda x: len(x["shared_axioms"]), reverse=True)
    
    table = Table(title="🌉 Harmonization Opportunities")
    table.add_column("Domains", style="bold")
    table.add_column("Shared Axioms", style="green")
    table.add_column("Dissonance", style="cyan")
    
    for opp in opportunities[:10]:
        table.add_row(
            f"{opp['domains'][0]} ↔ {opp['domains'][1]}",
            ", ".join(opp["shared_axioms"]),
            f"{opp['dissonance']:.2f}",
        )
    
    console.print(table)


# Galois connections between domains (adjunctions)
GALOIS_CONNECTIONS = {
    ("discopy", "hott"): {
        "type": "categorical-adjunction",
        "left": "Cup/Cap (rigid duals)",
        "right": "Unit/Counit formalization",
        "bridge": "Both formalize adjunctions; DisCoPy computational, HoTT foundational",
        "confirmed": True,
    },
    ("cerebrum", "gflownet"): {
        "type": "flow-optimization",
        "left": "Free energy minimization",
        "right": "Flow matching (forward/backward)",
        "bridge": "Both minimize divergence via dynamics",
        "confirmed": False,
    },
    ("graphcast", "discopy"): {
        "type": "encoder-decoder",
        "left": "Grid2Mesh (encode)",
        "right": "Mesh2Grid (decode)",
        "bridge": "Compositional message-passing on graphs",
        "confirmed": False,
    },
    ("petri", "discopy"): {
        "type": "categorical-semantics",
        "left": "Reaction network (Petri net)",
        "right": "String diagram (hypergraph)",
        "bridge": "Both open systems with operad composition",
        "confirmed": False,
    },
    ("hott", "poly"): {
        "type": "dependent-types",
        "left": "Path types (identity)",
        "right": "Polynomial functors (containers)",
        "bridge": "Both model dependent/indexed families",
        "confirmed": False,
    },
    ("composio", "discopy"): {
        "type": "tool-composition",
        "left": "Discovery (expand tool options)",
        "right": "Execution (collapse to result)",
        "bridge": "Sequential composition of operations",
        "confirmed": False,
    },
}


def find_galois_connection(domain_a: str, domain_b: str) -> dict | None:
    """Find Galois connection between two domains."""
    key = (domain_a, domain_b)
    conn = GALOIS_CONNECTIONS.get(key)
    if conn:
        return {"domains": key, **conn}
    key_rev = (domain_b, domain_a)
    conn = GALOIS_CONNECTIONS.get(key_rev)
    if conn:
        return {"domains": key_rev, **conn}
    return None


def display_galois_connections():
    """Display all known Galois connections."""
    table = Table(title="🔗 Galois Connections (Adjunctions)")
    table.add_column("Domains", style="bold")
    table.add_column("Type", style="cyan")
    table.add_column("L ⊣ R", style="green")
    table.add_column("Confirmed", style="yellow")
    
    for (a, b), conn in GALOIS_CONNECTIONS.items():
        table.add_row(
            f"{a} ↔ {b}",
            conn["type"],
            f"{conn['left'][:20]} ⊣ {conn['right'][:20]}",
            "✅" if conn["confirmed"] else "🔍",
        )
    
    console.print(table)


def find_missing_galois():
    """Find domain pairs that might have undetected Galois connections."""
    domains = list(DOMAIN_PROFILES.keys())
    covered = set()
    for (a, b) in GALOIS_CONNECTIONS.keys():
        covered.add((a, b))
        covered.add((b, a))
    
    missing = []
    for i, a in enumerate(domains):
        for b in domains[i+1:]:
            if (a, b) not in covered and (b, a) not in covered:
                # Check if they share composition structure
                prof_a = DOMAIN_PROFILES[a]
                prof_b = DOMAIN_PROFILES[b]
                if prof_a.get("compose") and prof_b.get("compose"):
                    missing.append({
                        "domains": (a, b),
                        "compose_a": prof_a["compose"],
                        "compose_b": prof_b["compose"],
                        "reason": "Different composition models may hide adjunction"
                    })
    
    table = Table(title="❓ Missing Galois Connections (candidates)")
    table.add_column("Domains", style="bold")
    table.add_column("Compose A")
    table.add_column("Compose B")
    table.add_column("Reason", style="dim")
    
    for m in missing[:10]:
        table.add_row(
            f"{m['domains'][0]} ↔ {m['domains'][1]}",
            m["compose_a"],
            m["compose_b"],
            m["reason"][:40],
        )
    
    console.print(table)


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) < 2:
        console.print("[bold]Harmonization Engine[/bold]")
        console.print()
        console.print("Commands:")
        console.print("  matrix     - Display full dissonance matrix")
        console.print("  domain X   - Show profile for domain X")
        console.print("  pair A B   - Compute dissonance between A and B")
        console.print("  bridge     - Find harmonization opportunities")
        console.print("  galois     - Show known Galois connections")
        console.print("  missing    - Find missing Galois connections")
        console.print()
        console.print("Domains:", ", ".join(DOMAIN_PROFILES.keys()))
        sys.exit(0)
    
    cmd = sys.argv[1]
    
    if cmd == "matrix":
        display_dissonance_matrix()
    elif cmd == "domain" and len(sys.argv) > 2:
        display_domain_profile(sys.argv[2])
    elif cmd == "pair" and len(sys.argv) > 3:
        result = compute_dissonance(sys.argv[2], sys.argv[3])
        console.print_json(data=result)
    elif cmd == "bridge":
        find_harmonization_opportunities()
    elif cmd == "galois":
        display_galois_connections()
    elif cmd == "missing":
        find_missing_galois()
    else:
        console.print(f"[red]Unknown command: {cmd}[/red]")
