#!/usr/bin/env python3
"""
Port Interface Coloring and Random Walk Launcher
GF(3) balanced skill graph traversal with deterministic coloring

Triad Colors (from gay-mcp seed 7449368709244611695):
  - #CA3E0E (Trit 0)  - Ergodic/Coordinator
  - #97B2DD (Trit +1) - Plus/Generator
  - #186FA5 (Trit -1) - Minus/Consumer
"""

import random
import hashlib
from dataclasses import dataclass
from enum import IntEnum
from pathlib import Path
from typing import List, Dict, Tuple, Optional

class Trit(IntEnum):
    MINUS = -1
    ERGODIC = 0
    PLUS = 1

@dataclass
class PortInterface:
    name: str
    color: str
    trit: Trit
    connections: List[str]

@dataclass
class Skill:
    name: str
    trit: Trit
    color: str
    ports: List[PortInterface]

# GF(3) Triad Colors
TRIAD_COLORS = {
    Trit.ERGODIC: "#CA3E0E",
    Trit.PLUS: "#97B2DD", 
    Trit.MINUS: "#186FA5",
}

# Extended palette for port interfaces
PORT_PALETTE = [
    "#89E2E1", "#8CD023", "#F87AD5", "#D778F4", 
    "#9C6B30", "#DC789E", "#C54C81", "#8CB7F1", "#AB3535"
]

def derive_trit(name: str) -> Trit:
    """Derive trit from skill name hash for GF(3) assignment"""
    h = int(hashlib.sha256(name.encode()).hexdigest()[:8], 16)
    return Trit((h % 3) - 1)

def derive_port_color(port_name: str, palette: List[str]) -> str:
    """Derive port color from name hash"""
    h = int(hashlib.sha256(port_name.encode()).hexdigest()[:8], 16)
    return palette[h % len(palette)]

# Core MCP Port Interfaces (from Nickel types)
MCP_PORTS = [
    PortInterface("JsonRpcRequest", PORT_PALETTE[0], Trit.PLUS, ["method", "params"]),
    PortInterface("JsonRpcResponse", PORT_PALETTE[1], Trit.MINUS, ["result", "error"]),
    PortInterface("StdioTransport", PORT_PALETTE[2], Trit.ERGODIC, ["command", "args", "env"]),
    PortInterface("HttpTransport", PORT_PALETTE[3], Trit.ERGODIC, ["url", "headers", "sse_endpoint"]),
    PortInterface("ToolDefinition", PORT_PALETTE[4], Trit.PLUS, ["name", "description", "inputSchema"]),
    PortInterface("ToolResult", PORT_PALETTE[5], Trit.MINUS, ["content", "isError"]),
    PortInterface("ResourceTemplate", PORT_PALETTE[6], Trit.PLUS, ["uriTemplate", "mimeType"]),
    PortInterface("PromptMessage", PORT_PALETTE[7], Trit.ERGODIC, ["role", "content"]),
    PortInterface("SamplingRequest", PORT_PALETTE[8], Trit.PLUS, ["messages", "maxTokens"]),
]

# Verify GF(3) conservation for MCP ports
def verify_port_conservation(ports: List[PortInterface]) -> bool:
    """Verify sum of trits = 0 (mod 3)"""
    total = sum(p.trit for p in ports)
    return total % 3 == 0

class SkillGraph:
    """Skill graph with GF(3) colored edges for random walks"""
    
    def __init__(self, skill_dir: Path):
        self.skills: Dict[str, Skill] = {}
        self.adjacency: Dict[str, List[str]] = {}
        self._load_skills(skill_dir)
        
    def _load_skills(self, skill_dir: Path):
        """Load all skills from directory"""
        for skill_path in sorted(skill_dir.iterdir()):
            if skill_path.is_dir():
                name = skill_path.name
                trit = derive_trit(name)
                color = TRIAD_COLORS[trit]
                self.skills[name] = Skill(name, trit, color, [])
                self.adjacency[name] = []
        
        # Build adjacency based on GF(3) compatibility
        skill_names = list(self.skills.keys())
        for i, s1 in enumerate(skill_names):
            for s2 in skill_names[i+1:]:
                # Connect if trits form valid pair (can complete triad)
                if (self.skills[s1].trit + self.skills[s2].trit) % 3 in [-1, 0, 1]:
                    self.adjacency[s1].append(s2)
                    self.adjacency[s2].append(s1)
    
    def random_walk(self, start: str, steps: int, seed: int = 42) -> List[Tuple[str, Trit]]:
        """Execute GF(3) conserving random walk"""
        rng = random.Random(seed)
        path = [(start, self.skills[start].trit)]
        current = start
        trit_sum = self.skills[start].trit
        
        for _ in range(steps):
            neighbors = self.adjacency.get(current, [])
            if not neighbors:
                break
            
            # Prefer moves that maintain GF(3) balance
            balanced = [n for n in neighbors 
                       if (trit_sum + self.skills[n].trit) % 3 == 0]
            if balanced and rng.random() > 0.3:
                next_skill = rng.choice(balanced)
            else:
                next_skill = rng.choice(neighbors)
            
            current = next_skill
            trit_sum = (trit_sum + self.skills[current].trit) % 3
            path.append((current, self.skills[current].trit))
        
        return path
    
    def launch_parallel_walks(self, n_walks: int = 3, steps: int = 10) -> Dict[int, List]:
        """Launch n parallel random walks from different triads"""
        results = {}
        
        # Group skills by trit
        by_trit = {t: [] for t in Trit}
        for name, skill in self.skills.items():
            by_trit[skill.trit].append(name)
        
        for i, trit in enumerate(Trit):
            if by_trit[trit]:
                start = by_trit[trit][i % len(by_trit[trit])]
                results[int(trit)] = self.random_walk(start, steps, seed=42 + i)
        
        return results

def main():
    skill_dir = Path("/Users/bob/ies/plurigrid-asi-skillz/skills")
    
    print("=" * 60)
    print("PORT INTERFACE COLORING")
    print("=" * 60)
    
    print("\nMCP Port Interfaces:")
    for port in MCP_PORTS:
        trit_sym = {Trit.MINUS: "-1", Trit.ERGODIC: " 0", Trit.PLUS: "+1"}[port.trit]
        print(f"  {port.color} [{trit_sym}] {port.name}")
        print(f"         └─ {', '.join(port.connections)}")
    
    conservation = verify_port_conservation(MCP_PORTS)
    print(f"\nGF(3) Conservation: {'✓' if conservation else '✗'} (sum mod 3 = {sum(p.trit for p in MCP_PORTS) % 3})")
    
    print("\n" + "=" * 60)
    print("SKILL GRAPH RANDOM WALKS")
    print("=" * 60)
    
    graph = SkillGraph(skill_dir)
    print(f"\nLoaded {len(graph.skills)} skills")
    
    # Count by trit
    by_trit = {t: 0 for t in Trit}
    for skill in graph.skills.values():
        by_trit[skill.trit] += 1
    
    print(f"\nTrit Distribution:")
    for trit, count in by_trit.items():
        print(f"  {TRIAD_COLORS[trit]} [{trit.name:8}]: {count}")
    
    print(f"\nBalance: {sum(by_trit[t] * t for t in Trit) % 3 == 0 and '✓ GF(3) conserved' or '✗ Imbalanced'}")
    
    print("\n" + "-" * 60)
    print("Launching 3 parallel random walks (10 steps each)...")
    print("-" * 60)
    
    walks = graph.launch_parallel_walks(n_walks=3, steps=10)
    
    for trit_val, path in walks.items():
        trit = Trit(trit_val)
        print(f"\n[{trit.name} walk] Starting from {path[0][0]}:")
        for i, (skill, t) in enumerate(path):
            arrow = "→ " if i > 0 else "  "
            print(f"  {arrow}{skill} ({'+' if t > 0 else ''}{t})")
        
        # Verify walk conservation
        walk_sum = sum(t for _, t in path) % 3
        print(f"  Walk sum mod 3 = {walk_sum}")

if __name__ == "__main__":
    main()
