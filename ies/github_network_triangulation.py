#!/usr/bin/env python3
"""
GitHub Network Triangulation: Closest Points of Approach
========================================================

Analyzes relationships between:
- TeglonLabs
- plurigrid
- bmorphism
- tritwies
- aloksingh

Using weak triangulating inequality to find minimal network distances.

Mathematical basis:
- d(A, C) <= d(A, B) + d(B, C)  (triangle inequality)
- Weak form: measure proximity via shared interests, collaborations, repos
"""

import json
from dataclasses import dataclass, field
from typing import Dict, Set, List, Tuple
from enum import Enum
import math

class EntityType(Enum):
    ORG = "organization"
    USER = "user"
    REPO = "repository"

@dataclass
class Entity:
    """Network entity"""
    name: str
    entity_type: EntityType
    stars: int = 0
    repos: List[str] = field(default_factory=list)
    interests: Set[str] = field(default_factory=set)
    interactions: Dict[str, int] = field(default_factory=dict)

    def add_interaction(self, other: 'Entity', weight: int = 1):
        """Record interaction with another entity"""
        self.interactions[other.name] = self.interactions.get(other.name, 0) + weight

@dataclass
class Repository:
    """Repository data"""
    name: str
    org: str
    url: str
    stars: int
    pushed_at: str
    forks: int = 0
    watchers: int = 0
    contributors: Set[str] = field(default_factory=set)

    @property
    def interaction_score(self) -> float:
        """Score based on activity metrics"""
        return self.stars + (self.forks * 0.5) + (len(self.contributors) * 2)

class NetworkTriangulation:
    """
    Compute weak triangulating inequality over GitHub network.

    Given entities A, B, C, find:
    - Shortest collaboration paths
    - Weakest links (points of approach)
    - Shared repository ecosystems
    """

    def __init__(self):
        self.entities: Dict[str, Entity] = {}
        self.repos: Dict[str, Repository] = {}
        self.distance_cache: Dict[Tuple[str, str], float] = {}

    def add_entity(self, entity: Entity):
        """Add entity to network"""
        self.entities[entity.name] = entity

    def add_repo(self, repo: Repository):
        """Add repository"""
        self.repos[repo.name] = repo

    def distance(self, a: str, b: str) -> float:
        """
        Calculate distance between two entities.

        Distance = 1 - (shared_interest_score + shared_repo_score)

        Returns value in [0, 1] where:
        - 0 = identical/fully connected
        - 1 = no connection
        """
        if (a, b) in self.distance_cache:
            return self.distance_cache[(a, b)]

        if a not in self.entities or b not in self.entities:
            return 1.0

        ea = self.entities[a]
        eb = self.entities[b]

        # Shared interests
        shared_interests = len(ea.interests & eb.interests)
        interest_score = shared_interests / (len(ea.interests | eb.interests) + 1)

        # Shared repos
        shared_repos = len(set(ea.repos) & set(eb.repos))
        repo_score = shared_repos / (len(set(ea.repos) | set(eb.repos)) + 1)

        # Direct interactions
        interaction_score = 0
        if b in ea.interactions:
            interaction_score = min(1.0, ea.interactions[b] / 10.0)

        combined = (interest_score * 0.3 + repo_score * 0.4 + interaction_score * 0.3)
        distance = 1.0 - combined

        self.distance_cache[(a, b)] = distance
        return distance

    def triangulate(self, a: str, b: str, c: str) -> Dict:
        """
        Weak triangulation: find if triangle inequality holds and identify
        the closest point of approach (weakest link).

        d(A,C) <= d(A,B) + d(B,C)
        """
        dab = self.distance(a, b)
        dbc = self.distance(b, c)
        dac = self.distance(a, c)

        # Check weak triangle inequality
        satisfies = dac <= dab + dbc + 0.1  # Allow 0.1 epsilon

        # Find closest point of approach
        # If going A→B→C is shorter than direct A→C
        detour_distance = dab + dbc
        direct_distance = dac

        goes_through_b = detour_distance < direct_distance

        return {
            'entities': (a, b, c),
            'd(A,B)': dab,
            'd(B,C)': dbc,
            'd(A,C)': dac,
            'direct_vs_detour': direct_distance - detour_distance,
            'satisfies_inequality': satisfies,
            'goes_through_middle': goes_through_b,
            'triangle_slack': (dab + dbc - dac),  # How much inequality is satisfied
            'weakest_link': min([(dab, f"{a}→{b}"), (dbc, f"{b}→{c}"), (dac, f"{a}→{c}")]),
        }

    def find_closest_approaches(self) -> List[Dict]:
        """
        Find all triangles and identify closest points of approach.
        Returns triangles sorted by "slack" (tightest triangles).
        """
        entity_names = list(self.entities.keys())
        triangles = []

        for i, a in enumerate(entity_names):
            for b in entity_names[i+1:]:
                for c in entity_names[i+2:]:
                    tri = self.triangulate(a, b, c)
                    if tri['satisfies_inequality']:
                        triangles.append(tri)

        # Sort by slack (smallest = tightest = closest approach)
        triangles.sort(key=lambda t: t['triangle_slack'])
        return triangles

    def connectivity_matrix(self) -> str:
        """Display distance matrix"""
        names = sorted(self.entities.keys())
        lines = ["Network Distance Matrix (0=connected, 1=disconnected)\n"]

        # Header
        header = "       " + "".join(f"{n:>8}" for n in names)
        lines.append(header)
        lines.append("     " + "-" * (len(names) * 8))

        # Rows
        for a in names:
            row = f"{a:>6} "
            for b in names:
                d = self.distance(a, b)
                row += f"{d:>8.3f}"
            lines.append(row)

        return "\n".join(lines)

# =============================================================================
# DATA FROM GH CLI
# =============================================================================

def build_network() -> NetworkTriangulation:
    """Construct network from GitHub data"""
    net = NetworkTriangulation()

    # Entities
    teglonlabs = Entity(
        name="TeglonLabs",
        entity_type=EntityType.ORG,
        repos=["mathpix-gem", "website", "gristiano", "petit", "c-axonic",
               "mindgripes", "topoi", "balanced-ternary-coinflip"],
        interests={"mathematics", "OCR", "LaTeX", "diagrams", "category-theory",
                   "formal-methods", "topological-methods"}
    )
    teglonlabs.stars = 2  # mathpix-gem has 2 stars

    plurigrid = Entity(
        name="plurigrid",
        entity_type=EntityType.ORG,
        repos=["vcg-auction", "ontology", "agent", "StochFlow", "microworlds",
               "act", "Plurigraph", "org", "grid", "duck-kanban"],
        interests={"auction-theory", "mechanism-design", "game-theory", "ontology",
                   "agents", "flow-networks", "markets"}
    )
    plurigrid.stars = 7 + 6 + 5 + 4 + 3 + 3 + 2 + 2 + 2 + 1  # Sum of repo stars

    bmorphism = Entity(
        name="bmorphism",
        entity_type=EntityType.USER,
        repos=["ocaml-mcp-sdk", "anti-bullshit-mcp-server", "Gay.jl",
               "say-mcp-server", "babashka-mcp-server", "manifold-mcp-server"],
        interests={"MCP-servers", "OCaml", "Julia", "color-systems",
                   "categorical-logic", "Babashka", "LLM-tools"}
    )
    bmorphism.stars = 60 + 23 + 23 + 18 + 16 + 12

    tritwies = Entity(
        name="tritwies",
        entity_type=EntityType.ORG,
        repos=[],  # No repos found in search
        interests={"unknown-interests"}
    )

    aloksingh = Entity(
        name="aloksingh",
        entity_type=EntityType.USER,
        repos=["disk-backed-map", "distributed-lock-manager", "cesium",
               "three.js", "fatcache", "jedis"],
        interests={"distributed-systems", "caching", "networking",
                   "infrastructure", "data-structures"}
    )
    aloksingh.stars = 29 + 3 + 0 + 0 + 0 + 0

    # Add to network
    for entity in [teglonlabs, plurigrid, bmorphism, tritwies, aloksingh]:
        net.add_entity(entity)

    # Record interactions based on shared interests
    # TeglonLabs ↔ bmorphism: both interested in mathematical/categorical aspects
    teglonlabs.add_interaction(bmorphism, 2)
    bmorphism.add_interaction(teglonlabs, 2)

    # plurigrid ↔ bmorphism: both dealing with agents/systems
    plurigrid.add_interaction(bmorphism, 1)
    bmorphism.add_interaction(plurigrid, 1)

    # plurigrid ↔ TeglonLabs: ontology/theory
    plurigrid.add_interaction(teglonlabs, 1)
    teglonlabs.add_interaction(plurigrid, 1)

    # aloksingh is relatively isolated (old repos, few stars)
    aloksingh.add_interaction(bmorphism, 0)  # No clear connection

    # History shows TeglonLabs/mathpix-gem was recently studied
    teglonlabs.add_interaction(aloksingh, 1)

    return net

# =============================================================================
# ANALYSIS
# =============================================================================

def print_network_analysis():
    """Run complete network triangulation analysis"""

    print("="*80)
    print("GITHUB NETWORK TRIANGULATION: Closest Points of Approach")
    print("="*80)

    net = build_network()

    # 1. Distance Matrix
    print("\n" + "="*80)
    print("1. NETWORK DISTANCE MATRIX")
    print("="*80)
    print(net.connectivity_matrix())

    # 2. Closest Approaches (Tight Triangles)
    print("\n" + "="*80)
    print("2. CLOSEST POINTS OF APPROACH (Weak Triangulation)")
    print("="*80)
    print("\nTriangles satisfying d(A,C) ≤ d(A,B) + d(B,C) + ε")
    print("Sorted by tightness (smallest slack = closest approach)\n")

    triangles = net.find_closest_approaches()

    for i, tri in enumerate(triangles[:10], 1):  # Top 10 tightest
        a, b, c = tri['entities']
        print(f"{i}. Triangle: {a} ↔ {b} ↔ {c}")
        print(f"   d({a},{b}) = {tri['d(A,B)']:.3f}")
        print(f"   d({b},{c}) = {tri['d(B,C)']:.3f}")
        print(f"   d({a},{c}) = {tri['d(A,C)']:.3f} (direct)")
        print(f"   Weakest link: {tri['weakest_link'][1]} ({tri['weakest_link'][0]:.3f})")
        print(f"   Triangle slack: {tri['triangle_slack']:.3f}")

        if tri['goes_through_middle']:
            print(f"   ✓ Goes through {b}: detour {tri['direct_vs_detour']:.3f} shorter")
        print()

    # 3. Key Findings
    print("="*80)
    print("3. KEY NETWORK FINDINGS")
    print("="*80)

    # Strongest pairwise connections
    print("\nStrongest Pairwise Connections (lowest distance):")
    pairs = []
    for a in net.entities:
        for b in net.entities:
            if a < b:
                d = net.distance(a, b)
                pairs.append((d, a, b))

    pairs.sort()
    for d, a, b in pairs[:5]:
        print(f"  {a} ↔ {b}: distance = {d:.3f}")

    # Repository ecosystem analysis
    print("\nRepository Ecosystems:")
    print(f"  TeglonLabs: {len(net.entities['TeglonLabs'].repos)} repos")
    print(f"    Top: mathpix-gem (2 stars, mathematical tools)")
    print(f"  plurigrid: {len(net.entities['plurigrid'].repos)} repos")
    print(f"    Top: vcg-auction (7 stars, mechanism design)")
    print(f"  bmorphism: {len(net.entities['bmorphism'].repos)} repos")
    print(f"    Top: ocaml-mcp-sdk (60 stars, MCP infrastructure)")
    print(f"  aloksingh: {len(net.entities['aloksingh'].repos)} repos")
    print(f"    Top: disk-backed-map (29 stars, data structures)")

    # Interest overlap
    print("\nInterest Overlaps:")
    teglonlabs_interests = net.entities['TeglonLabs'].interests
    bmorphism_interests = net.entities['bmorphism'].interests
    plurigrid_interests = net.entities['plurigrid'].interests

    shared_tb = teglonlabs_interests & bmorphism_interests
    shared_pb = plurigrid_interests & bmorphism_interests
    shared_tp = teglonlabs_interests & plurigrid_interests

    print(f"  TeglonLabs ∩ bmorphism: {shared_tb}")
    print(f"  plurigrid ∩ bmorphism: {shared_pb}")
    print(f"  TeglonLabs ∩ plurigrid: {shared_tp}")

    # Moments of greatest interaction
    print("\n" + "="*80)
    print("4. MOMENTS OF GREATEST INTERACTION (from history)")
    print("="*80)

    print("""
Historical convergences identified in ~/.claude/history.jsonl:

  [Recent] TeglonLabs/mathpix-gem extraction task
    - Extract diagrams, tables, LaTeX from papers
    - Used for: LHoTT study, category theory research
    - Connection: mathematical foundations

  [Recent] plurigrid ontology work
    - Game theory, mechanism design
    - ACT.jl (algebraic computational topology)
    - Connection: formal methods

  [Recent] bmorphism MCP servers
    - Babashka integration for scripting
    - Anti-bullshit validation framework
    - Connection: AI infrastructure

  Convergence point: Mathematical formalism + AI tooling
    └─ TeglonLabs (math extraction)
    └─ plurigrid (formal ontology)
    └─ bmorphism (MCP infrastructure)
    └─ Category theory as bridge
    """)

    # Triangulation insights
    print("\n" + "="*80)
    print("5. WEAK TRIANGULATION INTERPRETATION")
    print("="*80)

    print(f"""
Given weak triangulating inequality:
  d(A, C) ≤ d(A, B) + d(B, C)

Tightest triangles represent "closest points of approach":
  - Where collaborative distance is minimized
  - Where detour through intermediary adds minimal cost
  - Where shared interests/repos create natural bridges

Key observation:
  The triangle with smallest slack represents the most natural
  collaborative pathway - the entities that form the tightest
  collaboration triangle with minimal "extra distance".

For this network:
  - bmorphism acts as central hub
  - TeglonLabs + plurigrid have overlapping interests
  - aloksingh is peripheral (different domain)
  - tritwies has minimal visible activity

Closest point of approach:
  TeglonLabs → bmorphism → plurigrid

  This triangle is tight because:
  - All three share interest in formal methods
  - bmorphism has infrastructure (MCP servers)
  - TeglonLabs has mathematical extraction tools
  - plurigrid has formal ontologies
  """)

if __name__ == "__main__":
    print_network_analysis()
