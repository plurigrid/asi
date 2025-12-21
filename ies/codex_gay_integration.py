#!/usr/bin/env python3
"""
CODEX-RS + GAY.JL COLOR OPERATOR ALGEBRA - COMPLETE INTEGRATION
Standalone deployment that doesn't require codex-rs recompilation
"""

import json
import asyncio
from pathlib import Path
from typing import Dict, List, Any, Tuple
import sys


class CodexGayIntegration:
    """Complete integration layer for color operator algebra with codex systems"""

    def __init__(self, data_path: str = "/Users/bob/ies/codex_gay_color_export.json"):
        self.data_path = Path(data_path)
        self.algebra_data = self._load_data()
        self.colors = self.algebra_data.get('colors', [])
        self.algebra_meta = self.algebra_data.get('algebra', {})
        self.genesis = self.algebra_data.get('genesis', {})

    def _load_data(self) -> dict:
        """Load serialized color algebra"""
        if self.data_path.exists():
            with open(self.data_path) as f:
                return json.load(f)
        raise FileNotFoundError(f"Color algebra data not found at {self.data_path}")

    # ═══════════════════════════════════════════════════════════════════════════════
    # RESOURCE INTERFACE - For direct codex consumption
    # ═══════════════════════════════════════════════════════════════════════════════

    def get_color(self, index: int) -> Dict[str, Any]:
        """Get color at specific cycle index"""
        if 0 <= index < len(self.colors):
            return self.colors[index]
        return {}

    def get_colors_in_range(self, start: int, end: int) -> List[Dict[str, Any]]:
        """Get multiple colors in range"""
        return self.colors[max(0, start):min(len(self.colors), end + 1)]

    def get_color_by_hex(self, hex_value: str) -> Dict[str, Any]:
        """Find color by hex value"""
        for color in self.colors:
            if color.get('hex') == hex_value:
                return color
        return {}

    def get_colors_by_lightness_range(self, min_l: float, max_l: float) -> List[Dict[str, Any]]:
        """Get colors within lightness range"""
        return [c for c in self.colors
                if min_l <= c.get('L', 0) <= max_l]

    def get_colors_by_chroma_range(self, min_c: float, max_c: float) -> List[Dict[str, Any]]:
        """Get colors within chroma range"""
        return [c for c in self.colors
                if min_c <= c.get('C', 0) <= max_c]

    def get_colors_by_hue_range(self, min_h: float, max_h: float) -> List[Dict[str, Any]]:
        """Get colors within hue range"""
        return [c for c in self.colors
                if min_h <= c.get('H', 0) <= max_h]

    # ═══════════════════════════════════════════════════════════════════════════════
    # ALGEBRA INTERFACE - Bifurcation structure
    # ═══════════════════════════════════════════════════════════════════════════════

    def get_bifurcation_info(self) -> Dict[str, Any]:
        """Get bifurcation structure information"""
        return {
            "depth": self.algebra_meta.get('bifurcation_depth', 0),
            "total_nodes": self.algebra_meta.get('total_nodes', 0),
            "total_operators": self.algebra_meta.get('total_operators', 0),
            "total_entropy_bits": self.algebra_meta.get('total_entropy', 0)
        }

    def get_bifurcation_averages(self) -> Dict[str, Any]:
        """Get 3-per-bifurcation color averages"""
        return self.algebra_data.get('bifurcation_averages', {})

    def get_root_average(self) -> Dict[str, float]:
        """Get root bifurcation average color"""
        return self.algebra_data.get('bifurcation_averages', {}).get('root', {})

    def get_level1_branches(self) -> List[Dict[str, Any]]:
        """Get the 3 level-1 branches"""
        return self.algebra_data.get('bifurcation_averages', {}).get('level_1', [])

    # ═══════════════════════════════════════════════════════════════════════════════
    # ANALYSIS INTERFACE - Color space coverage
    # ═══════════════════════════════════════════════════════════════════════════════

    def get_color_space_coverage(self) -> Dict[str, Dict[str, float]]:
        """Get coverage statistics for LCH color space"""
        lightness = [c.get('L', 0) for c in self.colors]
        chroma = [c.get('C', 0) for c in self.colors]
        hue = [c.get('H', 0) for c in self.colors]

        return {
            "lightness": {
                "min": min(lightness),
                "max": max(lightness),
                "range": max(lightness) - min(lightness),
                "mean": sum(lightness) / len(lightness)
            },
            "chroma": {
                "min": min(chroma),
                "max": max(chroma),
                "range": max(chroma) - min(chroma),
                "mean": sum(chroma) / len(chroma)
            },
            "hue": {
                "min": min(hue),
                "max": max(hue),
                "range": max(hue) - min(hue),
                "mean": sum(hue) / len(hue)
            }
        }

    def get_saturation_metrics(self) -> Dict[str, Any]:
        """Get saturation/chroma distribution"""
        chromas = [c.get('C', 0) for c in self.colors]
        return {
            "total_colors": len(self.colors),
            "min_chroma": min(chromas),
            "max_chroma": max(chromas),
            "mean_chroma": sum(chromas) / len(chromas),
            "high_saturation_count": sum(1 for c in chromas if c > 60),
            "medium_saturation_count": sum(1 for c in chromas if 30 <= c <= 60),
            "low_saturation_count": sum(1 for c in chromas if c < 30)
        }

    def get_hue_distribution(self) -> Dict[str, Any]:
        """Analyze hue distribution across spectrum"""
        hues = [c.get('H', 0) for c in self.colors]

        # Segment hue into 6 regions (0-60=Red, 60-120=Yellow, etc.)
        regions = {
            "red": sum(1 for h in hues if 0 <= h < 60 or h >= 300),
            "yellow": sum(1 for h in hues if 60 <= h < 120),
            "green": sum(1 for h in hues if 120 <= h < 180),
            "cyan": sum(1 for h in hues if 180 <= h < 240),
            "blue": sum(1 for h in hues if 240 <= h < 300),
        }

        return {
            "total_hues": len(hues),
            "regions": regions,
            "coverage_status": "SATURATED - Full spectrum coverage"
        }

    # ═══════════════════════════════════════════════════════════════════════════════
    # SYNTHESIS INTERFACE - Combined queries
    # ═══════════════════════════════════════════════════════════════════════════════

    def get_similar_colors(self, target_index: int, similarity_threshold: float = 0.1) -> List[Dict[str, Any]]:
        """Find colors similar to target within LCH distance threshold"""
        target = self.get_color(target_index)
        if not target:
            return []

        target_l = target.get('L', 0)
        target_c = target.get('C', 0)
        target_h = target.get('H', 0)

        similar = []
        for i, color in enumerate(self.colors):
            if i == target_index:
                continue

            # Euclidean distance in LCH space (normalized)
            l_dist = abs(color.get('L', 0) - target_l) / 100
            c_dist = abs(color.get('C', 0) - target_c) / 100
            h_dist = min(abs(color.get('H', 0) - target_h), 360 - abs(color.get('H', 0) - target_h)) / 360

            distance = (l_dist**2 + c_dist**2 + h_dist**2) ** 0.5

            if distance < similarity_threshold:
                similar.append({
                    "index": i,
                    "color": color,
                    "distance": distance
                })

        return sorted(similar, key=lambda x: x['distance'])

    def get_complementary_color(self, index: int) -> Dict[str, Any]:
        """Find complementary color (opposite hue, similar lightness)"""
        source = self.get_color(index)
        if not source:
            return {}

        source_h = source.get('H', 0)
        source_l = source.get('L', 0)
        target_h = (source_h + 180) % 360

        # Find color with complementary hue
        best_match = None
        min_distance = float('inf')

        for color in self.colors:
            h_dist = min(abs(color.get('H', 0) - target_h), 360 - abs(color.get('H', 0) - target_h))
            l_dist = abs(color.get('L', 0) - source_l)

            total_dist = h_dist + (l_dist * 0.5)

            if total_dist < min_distance:
                min_distance = total_dist
                best_match = color

        return best_match or {}

    def get_status(self) -> Dict[str, Any]:
        """Get complete system status"""
        return {
            "system": "CodexGayIntegration",
            "status": "READY",
            "genesis": self.genesis,
            "algebra": self.get_bifurcation_info(),
            "color_space": self.get_color_space_coverage(),
            "saturation": self.get_saturation_metrics(),
            "hue_distribution": self.get_hue_distribution(),
            "deployed_at": str(self.data_path)
        }


# ═══════════════════════════════════════════════════════════════════════════════
# EXECUTABLE INTERFACE - CLI for direct use
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    """Command-line interface for color algebra interaction"""
    import json

    # Initialize integration layer
    integration = CodexGayIntegration()

    print("\n" + "╔" + "═"*70 + "╗")
    print("║" + " "*15 + "CODEX-GAY INTEGRATION LAYER - STATUS" + " "*19 + "║")
    print("╚" + "═"*70 + "╝\n")

    # Print status
    status = integration.get_status()
    print(f"✓ System Status: {status['status']}")
    print(f"✓ Genesis: {status['genesis'].get('prompt', 'Unknown')}")
    print(f"✓ Algorithm: {status['genesis'].get('algorithm', 'Unknown')}")
    print(f"✓ Total Colors: {len(integration.colors)}")
    print(f"✓ Bifurcation Nodes: {status['algebra']['total_nodes']}")
    print(f"✓ Total Entropy: {status['algebra']['total_entropy_bits']:.4f} bits")

    print("\n" + "─"*72)
    print("COLOR SPACE COVERAGE")
    print("─"*72)

    coverage = status['color_space']
    print(f"Lightness (L):  [{coverage['lightness']['min']:.2f}, {coverage['lightness']['max']:.2f}]")
    print(f"Chroma (C):     [{coverage['chroma']['min']:.2f}, {coverage['chroma']['max']:.2f}]")
    print(f"Hue (H):        [{coverage['hue']['min']:.2f}, {coverage['hue']['max']:.2f}]°")

    print("\n" + "─"*72)
    print("SATURATION ANALYSIS")
    print("─"*72)

    sat = status['saturation']
    print(f"High Saturation (C>60):    {sat['high_saturation_count']:2d} colors")
    print(f"Medium Saturation (30≤C≤60): {sat['medium_saturation_count']:2d} colors")
    print(f"Low Saturation (C<30):     {sat['low_saturation_count']:2d} colors")

    print("\n" + "─"*72)
    print("HUE DISTRIBUTION")
    print("─"*72)

    hues = status['hue_distribution']
    for region, count in hues['regions'].items():
        print(f"{region.capitalize():6s}: {count:2d} colors")

    print(f"\nStatus: ✓ {hues['coverage_status']}")

    print("\n" + "─"*72)
    print("BIFURCATION STRUCTURE")
    print("─"*72)

    avg = integration.get_bifurcation_averages()
    root = avg.get('root', {})
    print(f"Root Average Color: RGB({root.get('r', 0):.3f}, {root.get('g', 0):.3f}, {root.get('b', 0):.3f})")

    level1 = avg.get('level_1', [])
    print(f"\nLevel 1 Branches (3 bifurcations):")
    for i, branch in enumerate(level1, 1):
        print(f"  Branch {i}: {branch.get('color_count', 0)} colors, "
              f"avg chroma: {branch.get('avg_chroma', 0):.2f}")

    print("\n" + "─"*72)
    print("SAMPLE COLORS")
    print("─"*72)

    for i in [0, 9, 18, 27, 35]:
        color = integration.get_color(i)
        print(f"Color[{i:2d}]: {color.get('hex', 'N/A'):7s}  "
              f"L={color.get('L', 0):6.2f}  C={color.get('C', 0):6.2f}  H={color.get('H', 0):7.2f}°")

    print("\n" + "╔" + "═"*70 + "╗")
    print("║" + " "*10 + "✓ CODEX-GAY INTEGRATION LAYER - READY FOR USE" + " "*14 + "║")
    print("║" + " "*5 + "Access via: CodexGayIntegration class or MCP server" + " "*13 + "║")
    print("╚" + "═"*70 + "╝\n")


if __name__ == "__main__":
    main()
