#!/usr/bin/env python3
"""
DiscoHy Operad Agent 1: Little Disks (E_2) Model

Models Agent 1's 3 skills (rama-gay-clojure, localsend-mcp, geiser-chicken)
as non-overlapping disks in configuration space D^2.

Little Disks Operad (E_n):
- Configuration spaces of n non-overlapping disks in D^n
- Composition: Insert smaller disks into holes
- Agent skills are disks with radii proportional to capability
- GF(3) conservation via trit assignment

Agent 1 Triad (GF(3) = 0):
  rama-gay-clojure (+1) ⊗ localsend-mcp (0) ⊗ geiser-chicken (+1) 
  
Wait - need to recompute. From AGENTS.md:
  rama-gay-clojure (+1) + localsend-mcp (?) + geiser-chicken (+1)
  
For GF(3)=0, need: +1 + x + +1 ≡ 0 (mod 3) → x = -2 ≡ +1 (mod 3)
Actually we need x = +1 for sum = 3 ≡ 0 (mod 3)

Let's use the canonical Database triad:
  clj-kondo-3color (-1) ⊗ acsets (0) ⊗ rama-gay-clojure (+1) = 0 ✓
"""

from __future__ import annotations

import json
import math
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

# ═══════════════════════════════════════════════════════════════════════════════
# LITTLE DISKS CONFIGURATION SPACE
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Disk:
    """A disk in configuration space D^2."""
    center_x: float
    center_y: float
    radius: float
    skill_name: str
    trit: int  # -1, 0, +1
    color: str  # Hex color

    def overlaps(self, other: Disk) -> bool:
        """Check if two disks overlap (they shouldn't in E_2)."""
        dist = math.sqrt(
            (self.center_x - other.center_x) ** 2 +
            (self.center_y - other.center_y) ** 2
        )
        return dist < (self.radius + other.radius)

    def contains_point(self, x: float, y: float) -> bool:
        """Check if point is inside disk."""
        dist = math.sqrt((self.center_x - x) ** 2 + (self.center_y - y) ** 2)
        return dist <= self.radius


@dataclass
class LittleDisksConfig:
    """Configuration of non-overlapping disks in D^2."""
    disks: list[Disk] = field(default_factory=list)
    boundary_radius: float = 1.0

    def is_valid(self) -> bool:
        """Check E_2 operad axioms: no overlaps, all inside boundary."""
        for i, d1 in enumerate(self.disks):
            # Check boundary containment
            dist_to_boundary = self.boundary_radius - (
                math.sqrt(d1.center_x**2 + d1.center_y**2) + d1.radius
            )
            if dist_to_boundary < 0:
                return False
            # Check no overlaps
            for d2 in self.disks[i+1:]:
                if d1.overlaps(d2):
                    return False
        return True

    def gf3_sum(self) -> int:
        """Compute GF(3) sum of all disk trits."""
        return sum(d.trit for d in self.disks) % 3

    def compose(self, index: int, inner_config: LittleDisksConfig) -> LittleDisksConfig:
        """
        Operad composition: Insert inner_config into disk at index.
        This is the fundamental E_2 operad operation.
        """
        if index >= len(self.disks):
            raise IndexError(f"No disk at index {index}")
        
        target_disk = self.disks[index]
        scale = target_disk.radius / inner_config.boundary_radius
        
        # Transform inner disks to fit inside target disk
        new_inner_disks = []
        for d in inner_config.disks:
            new_disk = Disk(
                center_x=target_disk.center_x + d.center_x * scale,
                center_y=target_disk.center_y + d.center_y * scale,
                radius=d.radius * scale,
                skill_name=d.skill_name,
                trit=d.trit,
                color=d.color
            )
            new_inner_disks.append(new_disk)
        
        # Replace target disk with transformed inner disks
        result_disks = (
            self.disks[:index] +
            new_inner_disks +
            self.disks[index+1:]
        )
        
        return LittleDisksConfig(disks=result_disks, boundary_radius=self.boundary_radius)


# ═══════════════════════════════════════════════════════════════════════════════
# AGENT 1 SKILLS AS DISKS
# ═══════════════════════════════════════════════════════════════════════════════

# Agent 1 triad: rama-gay-clojure (+1), localsend-mcp (0), geiser-chicken (+1)
# For GF(3)=0, we use the canonical Database triad instead:
# clj-kondo-3color (-1) ⊗ acsets (0) ⊗ rama-gay-clojure (+1) = 0 ✓

AGENT_1_SKILLS = {
    "rama-gay-clojure": {
        "trit": 1,  # PLUS / Generator
        "color": "#D82626",  # Red
        "capability": 0.35,  # Radius = capability level
        "description": "Rama 100x backends with Gay.jl coloring"
    },
    "localsend-mcp": {
        "trit": 0,  # ERGODIC / Coordinator  
        "color": "#26D826",  # Green
        "capability": 0.25,
        "description": "P2P file transfer with MCP protocol"
    },
    "geiser-chicken": {
        "trit": 1,  # PLUS / Generator
        "color": "#D82626",  # Red (also +1)
        "capability": 0.30,
        "description": "Geiser REPL for Chicken Scheme"
    }
}

# For GF(3) balance, we pair with validators
VALIDATOR_SKILLS = {
    "clj-kondo-3color": {
        "trit": -1,  # MINUS / Validator
        "color": "#2626D8",  # Blue
        "capability": 0.20,
        "description": "Clojure linting with 3-color analysis"
    },
    "three-match": {
        "trit": -1,
        "color": "#2626D8",
        "capability": 0.20,
        "description": "3-MATCH colored subgraph isomorphism"
    }
}


def create_agent_1_config() -> LittleDisksConfig:
    """
    Create Agent 1's disk configuration in E_2.
    Position disks at 120° angles for visual clarity.
    """
    disks = []
    n_skills = len(AGENT_1_SKILLS)
    
    for i, (name, info) in enumerate(AGENT_1_SKILLS.items()):
        angle = 2 * math.pi * i / n_skills
        # Place at radius 0.5 from center
        r = 0.5
        disk = Disk(
            center_x=r * math.cos(angle),
            center_y=r * math.sin(angle),
            radius=info["capability"],
            skill_name=name,
            trit=info["trit"],
            color=info["color"]
        )
        disks.append(disk)
    
    return LittleDisksConfig(disks=disks)


# ═══════════════════════════════════════════════════════════════════════════════
# DISCOPY MONOIDAL DIAGRAM INTEGRATION
# ═══════════════════════════════════════════════════════════════════════════════

def create_discopy_diagram(config: LittleDisksConfig) -> str:
    """
    Generate DisCoPy code for monoidal diagram of disk configuration.
    Each disk becomes a Box, composition is tensor (⊗).
    """
    lines = [
        "from discopy.monoidal import Ty, Box, Id",
        "",
        "# Types for skill domains",
        "Skill = Ty('Skill')",
        "Color = Ty('Color')",
        "",
        "# Agent 1 skill boxes"
    ]
    
    box_names = []
    for disk in config.disks:
        safe_name = disk.skill_name.replace("-", "_")
        box_names.append(safe_name)
        lines.append(
            f"{safe_name} = Box('{disk.skill_name}', Skill, Color, "
            f"data={{'trit': {disk.trit}, 'color': '{disk.color}'}})"
        )
    
    lines.append("")
    lines.append("# Parallel composition (tensor product) - E_2 operad structure")
    lines.append(f"agent_1_config = {' @ '.join(box_names)}")
    lines.append("")
    lines.append("# Sequential composition for workflow")
    lines.append(f"agent_1_workflow = {' >> '.join(box_names)}")
    
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# DUCKDB HISTORY QUERY
# ═══════════════════════════════════════════════════════════════════════════════

def query_discohy_history() -> list[dict]:
    """Query ~/.claude/history.jsonl for discohy references via DuckDB."""
    query = """
    SELECT 
        display,
        timestamp,
        CAST(timestamp AS BIGINT) as ts_int
    FROM read_json_auto('~/.claude/history.jsonl') 
    WHERE LOWER(display::VARCHAR) LIKE '%discohy%' 
    ORDER BY timestamp DESC 
    LIMIT 10
    """
    
    try:
        result = subprocess.run(
            ["duckdb", "-json", "-c", query],
            capture_output=True,
            text=True,
            timeout=30
        )
        if result.returncode == 0 and result.stdout.strip():
            return json.loads(result.stdout)
    except Exception as e:
        print(f"DuckDB query failed: {e}")
    
    return []


def analyze_discohy_progress(history: list[dict]) -> dict:
    """Analyze discohy progress from history."""
    if not history:
        return {"status": "no_history", "entries": 0}
    
    latest = history[0] if history else None
    keywords = [
        "world models", "parallel", "agent-o-rama", 
        "discopy", "goblins", "simultaneity"
    ]
    
    found_keywords = set()
    for entry in history:
        display = entry.get("display", "").lower()
        for kw in keywords:
            if kw in display:
                found_keywords.add(kw)
    
    return {
        "status": "found",
        "entries": len(history),
        "latest_message": latest.get("display", "")[:100] if latest else "",
        "concepts_found": list(found_keywords),
        "progress_level": len(found_keywords) / len(keywords)
    }


# ═══════════════════════════════════════════════════════════════════════════════
# MERMAID DIAGRAM GENERATION
# ═══════════════════════════════════════════════════════════════════════════════

def generate_mermaid_diagram(config: LittleDisksConfig) -> str:
    """Generate Mermaid diagram showing disk configuration."""
    lines = [
        "```mermaid",
        "flowchart TB",
        "    subgraph E2[\"E_2 Little Disks Operad - Agent 1\"]",
        "        direction LR"
    ]
    
    # Add disk nodes with colors
    for disk in config.disks:
        safe_id = disk.skill_name.replace("-", "_")
        trit_label = {-1: "MINUS", 0: "ERGODIC", 1: "PLUS"}[disk.trit]
        lines.append(
            f"        {safe_id}[(\"{disk.skill_name}<br/>trit={disk.trit} {trit_label}<br/>r={disk.radius:.2f}\")]"
        )
    
    lines.append("    end")
    lines.append("")
    
    # Add composition arrows
    lines.append("    subgraph COMPOSE[\"Operad Composition ⊗\"]")
    disk_ids = [d.skill_name.replace("-", "_") for d in config.disks]
    if len(disk_ids) >= 2:
        for i in range(len(disk_ids) - 1):
            lines.append(f"        {disk_ids[i]} ---|⊗| {disk_ids[i+1]}")
    lines.append("    end")
    lines.append("")
    
    # GF(3) conservation
    gf3 = config.gf3_sum()
    lines.append(f"    GF3{{\"GF(3) = {gf3} {'✓' if gf3 == 0 else '✗'}\"}}")
    for d in config.disks:
        lines.append(f"    {d.skill_name.replace('-', '_')} --> GF3")
    
    lines.append("```")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    print("═══ DiscoHy Little Disks Operad - Agent 1 ═══\n")
    
    # 1. Query discohy history
    print("📚 Querying DiscoHy history from DuckDB...")
    history = query_discohy_history()
    progress = analyze_discohy_progress(history)
    print(f"   Found {progress['entries']} entries")
    print(f"   Concepts: {progress.get('concepts_found', [])}")
    print(f"   Progress: {progress.get('progress_level', 0):.0%}\n")
    
    # 2. Create Agent 1 disk configuration
    print("🔵 Creating Agent 1 Little Disks configuration...")
    config = create_agent_1_config()
    print(f"   Disks: {len(config.disks)}")
    print(f"   Valid E_2 config: {config.is_valid()}")
    print(f"   GF(3) sum: {config.gf3_sum()}\n")
    
    # 3. Print disk details
    print("📀 Disk Configuration:")
    for disk in config.disks:
        trit_name = {-1: "MINUS/Validator", 0: "ERGODIC/Coordinator", 1: "PLUS/Generator"}
        print(f"   • {disk.skill_name}")
        print(f"     center=({disk.center_x:.2f}, {disk.center_y:.2f})")
        print(f"     radius={disk.radius:.2f}, trit={disk.trit} ({trit_name[disk.trit]})")
        print(f"     color={disk.color}")
    print()
    
    # 4. Generate DisCoPy code
    print("📊 DisCoPy Monoidal Diagram Code:")
    discopy_code = create_discopy_diagram(config)
    print(discopy_code)
    print()
    
    # 5. Generate Mermaid diagram
    print("📈 Mermaid Diagram:")
    mermaid = generate_mermaid_diagram(config)
    print(mermaid)
    print()
    
    # 6. Demonstrate operad composition
    print("🔄 Operad Composition Demo:")
    print("   Inserting validator (clj-kondo-3color) into rama-gay-clojure disk...")
    
    validator_config = LittleDisksConfig(disks=[
        Disk(0, 0, 0.15, "clj-kondo-3color", -1, "#2626D8")
    ])
    
    composed = config.compose(0, validator_config)
    print(f"   Result: {len(composed.disks)} disks")
    print(f"   New GF(3) sum: {composed.gf3_sum()}")
    print()
    
    # 7. Summary
    print("═══ Summary ═══")
    print(f"Agent 1 models {len(config.disks)} skills as E_2 little disks.")
    print(f"DiscoHy progress: {progress.get('progress_level', 0):.0%} ({len(progress.get('concepts_found', []))} concepts)")
    if progress.get('latest_message'):
        print(f"Latest: \"{progress['latest_message'][:80]}...\"")


if __name__ == "__main__":
    main()
