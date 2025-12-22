"""
Pattern Types and Visualization for Ramanujan Walk Discovery
Seed: 0x42D | Trit: +1 (PLUS agent)

Pattern Categories:
- Convergent: walks that stabilize in small region
- Oscillating: periodic returns (high revisit rate)
- Exploratory: high entropy, uniform coverage
- Surprising: low probability, high value (GF(3) conservation)
"""

from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional
from enum import Enum, auto
import json

from ramanujan_walk import (
    RamanujanGraph, NonBacktrackingWalk, WalkTrajectory,
    PontryaginAnalyzer, OkLCH, SplitMix64, gf3_add, run_discovery
)

# ═══════════════════════════════════════════════════════════════════════════════
# PATTERN TYPE DEFINITIONS
# ═══════════════════════════════════════════════════════════════════════════════

class PatternCategory(Enum):
    """Canonical pattern categories from random walk analysis"""
    CONVERGENT = auto()    # Walks that stabilize
    OSCILLATING = auto()   # Periodic returns
    EXPLORATORY = auto()   # High entropy paths
    SURPRISING = auto()    # Low prob, high value

@dataclass
class PatternType:
    """
    Complete pattern type specification with:
    - Color (gay-mcp OkLCH)
    - Pontryagin character (frequency signature)
    - GF(3) properties (trit sum constraints)
    """
    category: PatternCategory
    color: OkLCH
    dominant_character: int  # 0, 1, or 2 for GF(3)
    entropy_range: Tuple[float, float]
    trit_constraint: str  # "any", "zero", "nonzero"
    
    # Semantic descriptors
    description: str = ""
    energy_interpretation: str = ""
    
    def to_dict(self) -> Dict:
        return {
            'category': self.category.name,
            'color_css': self.color.to_css(),
            'color_hex': self.color.to_hex(),
            'dominant_character': self.dominant_character,
            'character_omega': f"ω^{self.dominant_character}",
            'entropy_range': list(self.entropy_range),
            'trit_constraint': self.trit_constraint,
            'description': self.description,
            'energy': self.energy_interpretation
        }

# ═══════════════════════════════════════════════════════════════════════════════
# CANONICAL PATTERN DEFINITIONS
# ═══════════════════════════════════════════════════════════════════════════════

PATTERN_TYPES = {
    PatternCategory.CONVERGENT: PatternType(
        category=PatternCategory.CONVERGENT,
        color=OkLCH(L=0.55, C=0.12, H=180),  # Cyan - stable
        dominant_character=0,  # Trivial character (uniform)
        entropy_range=(0.0, 1.5),
        trit_constraint="any",
        description="Walks stabilizing in small vertex cluster",
        energy_interpretation="Low energy attractor basin"
    ),
    PatternCategory.OSCILLATING: PatternType(
        category=PatternCategory.OSCILLATING,
        color=OkLCH(L=0.60, C=0.18, H=270),  # Purple - cyclic
        dominant_character=1,  # ω character (cyclic)
        entropy_range=(0.5, 2.0),
        trit_constraint="nonzero",
        description="Periodic returns to visited vertices",
        energy_interpretation="Limit cycle behavior"
    ),
    PatternCategory.EXPLORATORY: PatternType(
        category=PatternCategory.EXPLORATORY,
        color=OkLCH(L=0.65, C=0.20, H=30),  # Orange - active
        dominant_character=2,  # ω² character (anti-cyclic)
        entropy_range=(2.5, 5.0),
        trit_constraint="any",
        description="High entropy diffusive exploration",
        energy_interpretation="Brownian mixing regime"
    ),
    PatternCategory.SURPRISING: PatternType(
        category=PatternCategory.SURPRISING,
        color=OkLCH(L=0.70, C=0.25, H=120),  # Green - novel
        dominant_character=0,  # Conservation requires trivial
        entropy_range=(1.0, 2.5),
        trit_constraint="zero",
        description="Low probability paths with GF(3) conservation",
        energy_interpretation="Rare fluctuation → emergent structure"
    )
}

# ═══════════════════════════════════════════════════════════════════════════════
# ASCII VISUALIZATION
# ═══════════════════════════════════════════════════════════════════════════════

class ASCIIVisualizer:
    """Generate ASCII art visualizations of graphs and walks"""
    
    TRIT_CHARS = {-1: '○', 0: '◎', 1: '●'}
    PATTERN_CHARS = {
        PatternCategory.CONVERGENT: '▼',
        PatternCategory.OSCILLATING: '◆',
        PatternCategory.EXPLORATORY: '★',
        PatternCategory.SURPRISING: '♦'
    }
    
    def __init__(self, graph: RamanujanGraph):
        self.graph = graph
        self.width = 60
        self.height = 20
    
    def render_graph_structure(self) -> str:
        """Render graph as adjacency structure"""
        lines = [
            "═══════════════════════════════════════════════════════════",
            f"  RAMANUJAN GRAPH: n={self.graph.n_vertices}, k={self.graph.degree}",
            f"  Spectral Gap: {self.graph.spectral_gap():.4f}",
            f"  Ramanujan Bound: {self.graph.ramanujan_bound():.4f}",
            f"  Is Ramanujan: {'✓' if self.graph.is_ramanujan() else '✗'}",
            "═══════════════════════════════════════════════════════════",
            ""
        ]
        
        # Show first 8 vertices with their connections
        lines.append("  Adjacency (first 8 vertices):")
        lines.append("  ───────────────────────────────")
        
        for v in range(min(8, self.graph.n_vertices)):
            trit = self.graph.vertex_trits[v]
            char = self.TRIT_CHARS[trit]
            neighbors = self.graph.adjacency.get(v, [])[:6]
            neighbor_str = ", ".join(str(n) for n in neighbors)
            if len(self.graph.adjacency.get(v, [])) > 6:
                neighbor_str += "..."
            lines.append(f"  {char} v{v:02d} → [{neighbor_str}]")
        
        if self.graph.n_vertices > 8:
            lines.append(f"  ... ({self.graph.n_vertices - 8} more vertices)")
        
        return "\n".join(lines)
    
    def render_trajectory(self, trajectory: WalkTrajectory, max_steps: int = 30) -> str:
        """Render walk trajectory as ASCII path"""
        if not trajectory.steps:
            return "  (empty trajectory)"
        
        lines = [
            f"  Pattern: {trajectory.pattern_type.upper()}",
            f"  Entropy: {trajectory.entropy:.3f}",
            f"  Trit Sum (mod 3): {trajectory.trit_sum}",
            "  ───────────────────────────────",
            "  Path:"
        ]
        
        # Build path visualization
        path_chars = []
        for i, step in enumerate(trajectory.steps[:max_steps]):
            char = self.TRIT_CHARS[step.trit]
            path_chars.append(f"{char}{step.vertex:02d}")
        
        # Wrap at 6 per line
        for i in range(0, len(path_chars), 6):
            chunk = path_chars[i:i+6]
            lines.append("  " + " → ".join(chunk))
        
        if len(trajectory.steps) > max_steps:
            lines.append(f"  ... ({len(trajectory.steps) - max_steps} more steps)")
        
        return "\n".join(lines)
    
    def render_pattern_summary(self, patterns: Dict[str, List[WalkTrajectory]]) -> str:
        """Render pattern distribution summary"""
        lines = [
            "═══════════════════════════════════════════════════════════",
            "  PATTERN DISTRIBUTION",
            "═══════════════════════════════════════════════════════════"
        ]
        
        total = sum(len(trajs) for trajs in patterns.values())
        
        for ptype, trajs in patterns.items():
            count = len(trajs)
            pct = (count / total * 100) if total > 0 else 0
            bar_len = int(pct / 2.5)  # Scale to 40 chars max
            
            category = PatternCategory[ptype.upper()]
            char = self.PATTERN_CHARS[category]
            pattern_def = PATTERN_TYPES[category]
            
            bar = '█' * bar_len + '░' * (40 - bar_len)
            lines.append(f"  {char} {ptype:12} │{bar}│ {count:3} ({pct:5.1f}%)")
            lines.append(f"    Color: {pattern_def.color.to_css()}")
        
        return "\n".join(lines)
    
    def render_pontryagin_spectrum(self, signatures: Dict) -> str:
        """Render Pontryagin dual analysis"""
        lines = [
            "",
            "═══════════════════════════════════════════════════════════",
            "  PONTRYAGIN DUAL SPECTRUM (Characters on GF(3))",
            "═══════════════════════════════════════════════════════════",
            "",
            "  Character ω^k where ω = e^(2πi/3):",
            "  ───────────────────────────────────",
            "    χ₀ = 1       (trivial - uniform)",
            "    χ₁ = ω       (cyclic rotation)",  
            "    χ₂ = ω²      (anti-cyclic)",
            ""
        ]
        
        for ptype, sig in signatures.items():
            spectrum = sig.get('spectrum', [0, 0, 0])
            dominant = sig.get('dominant', -1)
            interp = sig.get('interpretation', '')
            
            lines.append(f"  {ptype.upper()}:")
            lines.append(f"    Dominant: χ_{dominant} ({interp})")
            lines.append(f"    Spectrum: [{spectrum[0]:.2f}, {spectrum[1]:.2f}, {spectrum[2]:.2f}]")
            
            # Spectrum bar chart
            max_val = max(spectrum) if spectrum else 1
            for i, val in enumerate(spectrum):
                bar_len = int(val / max_val * 20) if max_val > 0 else 0
                bar = '▓' * bar_len
                lines.append(f"      χ_{i}: {bar}")
            lines.append("")
        
        return "\n".join(lines)

# ═══════════════════════════════════════════════════════════════════════════════
# JSON EXPORT
# ═══════════════════════════════════════════════════════════════════════════════

def export_patterns_json(results: Dict, graph: RamanujanGraph = None) -> Dict:
    """Export complete pattern analysis as JSON"""
    
    export = {
        'metadata': {
            'seed': '0x42D',
            'trit_agent': '+1 (PLUS)',
            'framework': 'Ramanujan Walk Pattern Discovery'
        },
        'pattern_types': {
            cat.name: pt.to_dict() 
            for cat, pt in PATTERN_TYPES.items()
        },
        'discovery_results': results,
        'color_palette': {
            'trit_minus': OkLCH.from_trit(-1).to_dict() if hasattr(OkLCH, 'to_dict') else OkLCH.from_trit(-1).to_css(),
            'trit_zero': OkLCH.from_trit(0).to_css(),
            'trit_plus': OkLCH.from_trit(1).to_css()
        },
        'gf3_algebra': {
            'elements': [-1, 0, 1],
            'addition_table': [
                [gf3_add(a, b) for b in [-1, 0, 1]]
                for a in [-1, 0, 1]
            ],
            'characters': [
                {'index': k, 'value': f"ω^{k}", 'omega': f"e^(2πi·{k}/3)"}
                for k in range(3)
            ]
        }
    }
    
    return export

# ═══════════════════════════════════════════════════════════════════════════════
# FULL VISUALIZATION PIPELINE  
# ═══════════════════════════════════════════════════════════════════════════════

def visualize_discovery(n_vertices: int = 32, degree: int = 4,
                        n_walks: int = 50, walk_length: int = 30,
                        seed: int = 0x42D) -> Tuple[str, Dict]:
    """
    Run discovery and generate complete visualization.
    
    Returns: (ascii_output, json_export)
    """
    # Build graph
    graph = RamanujanGraph(n_vertices=n_vertices, degree=degree)
    
    # Run walks
    walker = NonBacktrackingWalk(graph, seed=seed)
    patterns = walker.discover_patterns(n_walks=n_walks, walk_length=walk_length)
    
    # Analyze
    analyzer = PontryaginAnalyzer()
    signatures = analyzer.character_signature(patterns)
    
    # Get results
    results = run_discovery(n_vertices, degree, n_walks, walk_length, seed)
    
    # Visualize
    viz = ASCIIVisualizer(graph)
    
    ascii_parts = [
        "",
        "╔═══════════════════════════════════════════════════════════════╗",
        "║  RAMANUJAN COMPLEX RANDOM WALK - PATTERN DISCOVERY            ║",
        "║  Seed: 0x42D | Trit: +1 (PLUS Agent)                         ║",
        "╚═══════════════════════════════════════════════════════════════╝",
        "",
        viz.render_graph_structure(),
        "",
        viz.render_pattern_summary(patterns),
        viz.render_pontryagin_spectrum(signatures),
    ]
    
    # Add example trajectories
    ascii_parts.append("═══════════════════════════════════════════════════════════")
    ascii_parts.append("  SAMPLE TRAJECTORIES")
    ascii_parts.append("═══════════════════════════════════════════════════════════")
    
    for ptype, trajs in patterns.items():
        if trajs:
            ascii_parts.append(f"\n  [{ptype.upper()}]")
            ascii_parts.append(viz.render_trajectory(trajs[0]))
    
    ascii_output = "\n".join(ascii_parts)
    json_export = export_patterns_json(results, graph)
    
    return ascii_output, json_export

# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("\n🔬 Running Ramanujan Walk Pattern Discovery...\n")
    
    ascii_viz, json_data = visualize_discovery(
        n_vertices=32,
        degree=4, 
        n_walks=100,
        walk_length=40
    )
    
    print(ascii_viz)
    print("\n" + "═" * 60)
    print("  JSON EXPORT")
    print("═" * 60)
    print(json.dumps(json_data, indent=2, default=str)[:2000] + "\n  ...")
    
    # Save JSON
    with open('pattern_discovery_results.json', 'w') as f:
        json.dump(json_data, f, indent=2, default=str)
    print("\n  → Saved to pattern_discovery_results.json")
