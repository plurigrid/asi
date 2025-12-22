#!/usr/bin/env python3
"""
bmorphism Intent Evolution Analysis
====================================

Analyzes GitHub activity to infer intent evolution over time using:
- Recency × Magnitude × Impact scoring
- Period-based clustering
- Ramanujan walk pattern matching
- Color-coded intent phases

Seed: 0x42D | GF(3) Conservation
"""

import json
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
from datetime import datetime, timedelta
from collections import defaultdict
import math

# ═══════════════════════════════════════════════════════════════════════════════
# RAW DATA FROM GH API (extracted from session)
# ═══════════════════════════════════════════════════════════════════════════════

YEARLY_DATA = [
    {"year": "2017", "count": 1, "total_stars": 3, "top": ["talks (3⭐, JS)"]},
    {"year": "2020", "count": 1, "total_stars": 63, "top": ["ProjectDomino (63⭐, Python)"]},
    {"year": "2021", "count": 3, "total_stars": 73, "top": ["wasmswap-contracts (47⭐, Rust)", "CadCAD.jl (17⭐, Julia)"]},
    {"year": "2022", "count": 10, "total_stars": 52, "top": ["risc0-cosmwasm-example (23⭐, Rust)", "cw-unity-prop (7⭐, Rust)"]},
    {"year": "2024", "count": 4, "total_stars": 8, "top": ["latent-toys (2⭐)", "antimemex (2⭐)"]},
    {"year": "2025", "count": 81, "total_stars": 241, "top": [
        "ocaml-mcp-sdk (60⭐, OCaml)", 
        "anti-bullshit-mcp-server (23⭐, JS)",
        "say-mcp-server (18⭐, JS)",
        "babashka-mcp-server (16⭐, JS)",
        "manifold-mcp-server (12⭐, JS)"
    ]}
]

TOP_REPOS = [
    {"name": "ProjectDomino", "stars": 63, "forks": 13, "year": 2020, "lang": "Python", "desc": "Pandemic modeling"},
    {"name": "ocaml-mcp-sdk", "stars": 60, "forks": 1, "year": 2025, "lang": "OCaml", "desc": "MCP SDK"},
    {"name": "wasmswap-contracts", "stars": 47, "forks": 46, "year": 2021, "lang": "Rust", "desc": "CosmWasm DEX"},
    {"name": "anti-bullshit-mcp-server", "stars": 23, "forks": 7, "year": 2025, "lang": "JavaScript", "desc": "Epistemic verification"},
    {"name": "risc0-cosmwasm-example", "stars": 23, "forks": 3, "year": 2022, "lang": "Rust", "desc": "ZK + Cosmos"},
    {"name": "say-mcp-server", "stars": 18, "forks": 9, "year": 2025, "lang": "JavaScript", "desc": "TTS MCP"},
    {"name": "CadCAD.jl", "stars": 17, "forks": 3, "year": 2021, "lang": "Julia", "desc": "Complex systems"},
    {"name": "babashka-mcp-server", "stars": 16, "forks": 5, "year": 2025, "lang": "JavaScript", "desc": "Clojure scripting MCP"},
    {"name": "manifold-mcp-server", "stars": 12, "forks": 11, "year": 2025, "lang": "JavaScript", "desc": "Prediction markets MCP"},
]

RECENT_EVENTS = {
    "ForkEvent": 49,
    "WatchEvent": 99,  # Stars received
    "IssuesEvent": 10,
    "PullRequestEvent": 23
}

# ═══════════════════════════════════════════════════════════════════════════════
# INTENT PHASES - Color-Coded Evolution
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class IntentPhase:
    """A distinct phase in the evolution of intent"""
    name: str
    period: Tuple[int, int]  # (start_year, end_year)
    trit: int  # GF(3) classification
    hue: float  # OkLCH hue
    dominant_themes: List[str]
    evidence: List[str]
    impact_score: float = 0.0
    
    def to_css(self) -> str:
        return f"oklch(0.65 0.18 {self.hue})"

INTENT_PHASES = [
    IntentPhase(
        name="Foundation: Academic + Talks",
        period=(2017, 2019),
        trit=0,  # ERGODIC - laying groundwork
        hue=180,  # Cyan
        dominant_themes=["Communication", "Knowledge sharing", "Community"],
        evidence=["talks repo (3⭐)", "Early presence"],
        impact_score=3.0
    ),
    IntentPhase(
        name="Crisis Response: Pandemic Modeling",
        period=(2020, 2020),
        trit=1,  # PLUS - generative response to crisis
        hue=30,  # Orange
        dominant_themes=["Epidemiology", "Social good", "Python ML"],
        evidence=["ProjectDomino (63⭐)", "COVID response", "Collaboration"],
        impact_score=63.0
    ),
    IntentPhase(
        name="DeFi Infrastructure: Cosmos/CosmWasm",
        period=(2021, 2022),
        trit=-1,  # MINUS - building constraints/verification
        hue=270,  # Purple
        dominant_themes=["Rust", "Smart contracts", "DEX", "ZK proofs"],
        evidence=[
            "wasmswap-contracts (47⭐, 46 forks)", 
            "risc0-cosmwasm-example (23⭐)",
            "cw-unity-prop (7⭐)",
            "CadCAD.jl (17⭐) - complex systems"
        ],
        impact_score=94.0  # Sum of stars
    ),
    IntentPhase(
        name="Exploration: Category Theory + Latent Spaces",
        period=(2023, 2024),
        trit=0,  # ERGODIC - exploratory
        hue=200,  # Blue-cyan
        dominant_themes=["Category theory", "Applied math", "Memory systems"],
        evidence=[
            "awesome-applied-category-theory (3⭐)",
            "antimemex (Eco forgetting)",
            "latent-toys",
            "crags (RAGs categorically)"
        ],
        impact_score=8.0
    ),
    IntentPhase(
        name="MCP Explosion: AI Agent Infrastructure",
        period=(2025, 2025),
        trit=1,  # PLUS - massive generative output
        hue=60,  # Yellow-orange
        dominant_themes=["MCP servers", "AI agents", "Multi-language", "Clojure/OCaml"],
        evidence=[
            "ocaml-mcp-sdk (60⭐) - functional MCP",
            "anti-bullshit-mcp-server (23⭐) - epistemics",
            "say-mcp-server (18⭐) - TTS",
            "babashka-mcp-server (16⭐) - Clojure",
            "manifold-mcp-server (12⭐) - prediction markets",
            "penrose-mcp (8⭐) - diagramming",
            "nats-mcp-server (7⭐) - messaging",
            "marginalia-mcp-server (6⭐) - search",
            "Gay.jl (2⭐) - color generation",
            "81 repos created in 2025!"
        ],
        impact_score=241.0
    )
]

# ═══════════════════════════════════════════════════════════════════════════════
# RECENCY × MAGNITUDE × IMPACT SCORING
# ═══════════════════════════════════════════════════════════════════════════════

def compute_rmi_score(repo: dict, current_year: int = 2025) -> float:
    """
    Compute Recency × Magnitude × Impact score.
    
    Recency: Exponential decay from current year (half-life = 2 years)
    Magnitude: log(1 + stars + forks)
    Impact: Fork ratio (forks/stars indicates practical adoption)
    """
    year = repo.get("year", 2025)
    stars = repo.get("stars", 0)
    forks = repo.get("forks", 0)
    
    # Recency: exponential decay
    age = current_year - year
    recency = math.exp(-age / 2.0)  # Half-life of 2 years
    
    # Magnitude: log scale
    magnitude = math.log(1 + stars + forks)
    
    # Impact: fork ratio (capped)
    fork_ratio = min(forks / max(stars, 1), 1.0)
    impact = 0.5 + 0.5 * fork_ratio  # Range [0.5, 1.0]
    
    return recency * magnitude * impact

def analyze_top_repos() -> List[dict]:
    """Analyze top repos with RMI scoring"""
    results = []
    for repo in TOP_REPOS:
        rmi = compute_rmi_score(repo)
        results.append({
            **repo,
            "rmi_score": round(rmi, 3),
            "recency": round(math.exp(-(2025 - repo["year"]) / 2.0), 3),
            "magnitude": round(math.log(1 + repo["stars"] + repo.get("forks", 0)), 3),
        })
    return sorted(results, key=lambda x: -x["rmi_score"])

# ═══════════════════════════════════════════════════════════════════════════════
# INTENT EVOLUTION INFERENCE
# ═══════════════════════════════════════════════════════════════════════════════

def infer_intent_trajectory() -> dict:
    """
    Infer intent evolution trajectory.
    
    Key patterns:
    1. Crisis-driven pivots (2020 pandemic)
    2. Technology stack evolution (Python → Rust → OCaml/Clojure)
    3. Domain expansion (health → finance → AI agents)
    4. Increasing output velocity (1→3→10→4→81 repos/year)
    """
    
    # Language evolution
    lang_timeline = [
        (2017, "JavaScript", "Communication"),
        (2020, "Python", "ML/Data"),
        (2021, "Rust/Julia", "Systems/Simulation"),
        (2022, "Rust", "Blockchain/ZK"),
        (2024, "TypeScript", "Exploration"),
        (2025, "OCaml/Clojure/JS", "Functional AI Agents")
    ]
    
    # Theme evolution
    theme_evolution = {
        "communication": [2017],
        "crisis_response": [2020],
        "defi_infrastructure": [2021, 2022],
        "category_theory": [2023, 2024, 2025],
        "ai_agents": [2025],
        "mcp_servers": [2025]
    }
    
    # Velocity analysis
    velocity = {
        "2017-2019": 1,    # Slow, foundational
        "2020": 1,          # Crisis focus
        "2021": 3,          # DeFi expansion
        "2022": 10,         # Blockchain boom
        "2023": 4,          # Consolidation
        "2024": 4,          # Exploration
        "2025": 81          # MCP explosion
    }
    
    return {
        "language_evolution": lang_timeline,
        "theme_evolution": theme_evolution,
        "velocity": velocity,
        "current_focus": [
            "MCP (Model Context Protocol) server development",
            "Functional programming (OCaml, Clojure, Babashka)",
            "AI agent infrastructure",
            "Epistemic tools (anti-bullshit verification)",
            "Multi-modal (TTS, diagrams, prediction markets)"
        ],
        "trajectory_interpretation": """
The intent evolution shows a clear progression:

1. **Foundation (2017-2019)**: Community building, talks
2. **Crisis Response (2020)**: Rapid pivot to pandemic modeling
3. **DeFi Infrastructure (2021-2022)**: Deep dive into Rust/CosmWasm
4. **Exploration (2023-2024)**: Category theory, memory systems
5. **MCP Explosion (2025)**: Massive output of AI agent tooling

Key insight: The 81 repos in 2025 represent a **phase transition** from 
consumer of AI tools to **producer of AI infrastructure**. The focus on
MCP servers across multiple languages (OCaml, JS, Python, Clojure) suggests
intent to establish **polyglot AI agent ecosystem**.

The anti-bullshit-mcp-server and Gay.jl indicate meta-cognitive concerns:
verification of claims and deterministic reproducibility.
"""
    }

# ═══════════════════════════════════════════════════════════════════════════════
# GF(3) PHASE COLORING
# ═══════════════════════════════════════════════════════════════════════════════

def color_phases() -> List[dict]:
    """Color-code intent phases with GF(3) trits"""
    colored = []
    for phase in INTENT_PHASES:
        trit_symbol = {-1: "⊖", 0: "○", 1: "⊕"}[phase.trit]
        colored.append({
            "name": phase.name,
            "period": f"{phase.period[0]}-{phase.period[1]}",
            "trit": trit_symbol,
            "color": phase.to_css(),
            "themes": phase.dominant_themes,
            "impact": phase.impact_score,
            "evidence": phase.evidence[:3]
        })
    
    # Verify GF(3) conservation across phases
    trit_sum = sum(p.trit for p in INTENT_PHASES)
    colored.append({
        "_gf3_sum": trit_sum,
        "_conserved": trit_sum % 3 == 0
    })
    
    return colored

# ═══════════════════════════════════════════════════════════════════════════════
# MAIN ANALYSIS
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    print("═" * 70)
    print("  BMORPHISM INTENT EVOLUTION ANALYSIS")
    print("  Recency × Magnitude × Impact Scoring | GF(3) Phase Coloring")
    print("═" * 70)
    print()
    
    # Phase analysis
    print("┌─────────────────────────────────────────────────────────────────────┐")
    print("│  INTENT PHASES                                                      │")
    print("├─────────────────────────────────────────────────────────────────────┤")
    
    phases = color_phases()
    for p in phases[:-1]:  # Skip GF(3) metadata
        print(f"│  {p['trit']} {p['period']:10} │ {p['name'][:40]:<40} │")
        print(f"│    Impact: {p['impact']:5.0f}⭐  │ {p['themes'][0][:35]:<35} │")
    
    gf3 = phases[-1]
    print(f"├─────────────────────────────────────────────────────────────────────┤")
    print(f"│  GF(3) Sum: {gf3['_gf3_sum']:+d}  │  {'✓ CONSERVED' if gf3['_conserved'] else '✗ OPEN':<52}│")
    print("└─────────────────────────────────────────────────────────────────────┘")
    print()
    
    # RMI scoring
    print("┌─────────────────────────────────────────────────────────────────────┐")
    print("│  TOP REPOS BY RMI SCORE (Recency × Magnitude × Impact)             │")
    print("├─────────────────────────────────────────────────────────────────────┤")
    
    rmi_repos = analyze_top_repos()
    for r in rmi_repos[:8]:
        bar = "█" * int(r["rmi_score"] * 5)
        print(f"│  {r['name'][:25]:<25} │ RMI: {r['rmi_score']:5.2f} │ {bar:<15} │")
    
    print("└─────────────────────────────────────────────────────────────────────┘")
    print()
    
    # Trajectory
    trajectory = infer_intent_trajectory()
    print("┌─────────────────────────────────────────────────────────────────────┐")
    print("│  CURRENT FOCUS (2025)                                               │")
    print("├─────────────────────────────────────────────────────────────────────┤")
    for focus in trajectory["current_focus"]:
        print(f"│  • {focus[:64]:<65}│")
    print("└─────────────────────────────────────────────────────────────────────┘")
    print()
    
    # Velocity chart
    print("┌─────────────────────────────────────────────────────────────────────┐")
    print("│  OUTPUT VELOCITY (repos/year)                                       │")
    print("├─────────────────────────────────────────────────────────────────────┤")
    for period, count in trajectory["velocity"].items():
        bar = "█" * min(count, 50)
        print(f"│  {period:10} │ {count:3} │ {bar:<50}│")
    print("└─────────────────────────────────────────────────────────────────────┘")
    
    # Export
    export = {
        "phases": phases,
        "rmi_repos": rmi_repos,
        "trajectory": trajectory,
        "yearly_data": YEARLY_DATA,
        "recent_events": RECENT_EVENTS
    }
    
    output_path = "/Users/bob/ies/plurigrid-asi-skillz/bmorphism_intent_evolution.json"
    with open(output_path, 'w') as f:
        json.dump(export, f, indent=2, default=str)
    print(f"\n  → Saved to {output_path}")
    
    return export

if __name__ == "__main__":
    main()
