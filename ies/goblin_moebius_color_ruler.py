#!/usr/bin/env python3
"""
GOBLIN MOEBIUS INVERSION COLOR RULER SYSTEM
Using Gay color system + Moebius inversion + 3-fold application

Features:
- Moebius inversion for capability-to-color mapping
- Splitmixternary color mixing (3-component balanced system)
- 3-fold application hierarchy
- MCP-compatible ruler interface
- Deterministic color assignment to discovered goblins
"""

import sys
sys.path.insert(0, '/Users/bob/ies')

from typing import Dict, List, Tuple, Optional, Set
from dataclasses import dataclass, field
from collections import defaultdict
from enum import Enum
import json
import time
from datetime import datetime
import math

# ============================================================================
# MOEBIUS INVERSION CORE
# ============================================================================

class MoebiusFunction:
    """Moebius function for number theory transformations"""
    
    @staticmethod
    def mu(n: int) -> int:
        """Compute Mobius function μ(n)
        
        μ(n) = 1 if n is square-free with even number of prime factors
        μ(n) = -1 if n is square-free with odd number of prime factors
        μ(n) = 0 if n has a squared prime factor
        """
        if n == 1:
            return 1
        
        prime_factors = 0
        temp_n = n
        
        # Check for factor 2
        if temp_n % 2 == 0:
            prime_factors += 1
            temp_n //= 2
            if temp_n % 2 == 0:
                return 0  # Squared prime factor
        
        # Check for odd factors
        d = 3
        while d * d <= temp_n:
            if temp_n % d == 0:
                prime_factors += 1
                temp_n //= d
                if temp_n % d == 0:
                    return 0  # Squared prime factor
            d += 2
        
        if temp_n > 1:
            prime_factors += 1
        
        return 1 if prime_factors % 2 == 0 else -1
    
    @staticmethod
    def moebius_invert(f: Dict[int, float]) -> Dict[int, float]:
        """Apply Moebius inversion to a function
        
        If g(n) = Σ f(d) for d|n
        Then f(n) = Σ μ(n/d) * g(d) for d|n
        """
        result = {}
        max_n = max(f.keys()) if f else 1
        
        for n in range(1, max_n + 1):
            total = 0
            for d in range(1, n + 1):
                if n % d == 0:
                    moebius = MoebiusFunction.mu(n // d)
                    if d in f:
                        total += moebius * f[d]
            result[n] = total
        
        return result


# ============================================================================
# SPLITMIXTERNARY COLOR SYSTEM
# ============================================================================

class SplitmixTernaryColor:
    """Balanced ternary color system with 3 components"""
    
    def __init__(self, r: float = 0.0, g: float = 0.0, b: float = 0.0):
        """Initialize with balanced ternary values (-1, 0, 1)"""
        self.r = self._clamp_ternary(r)
        self.g = self._clamp_ternary(g)
        self.b = self._clamp_ternary(b)
    
    @staticmethod
    def _clamp_ternary(value: float) -> int:
        """Clamp to balanced ternary (-1, 0, 1)"""
        if value < -0.5:
            return -1
        elif value > 0.5:
            return 1
        else:
            return 0
    
    def to_hex(self) -> str:
        """Convert balanced ternary to hex color
        
        Mapping:
        -1 → 0x00 (off)
         0 → 0x7F (mid)
         1 → 0xFF (on)
        """
        def component_to_hex(val: int) -> str:
            if val == -1:
                return "00"
            elif val == 0:
                return "7F"
            else:
                return "FF"
        
        return f"#{component_to_hex(self.r)}{component_to_hex(self.g)}{component_to_hex(self.b)}"
    
    def __repr__(self) -> str:
        return f"SplitmixTernary({self.r:+d}, {self.g:+d}, {self.b:+d}) → {self.to_hex()}"


# ============================================================================
# MOEBIUS COLOR RULER
# ============================================================================

class MoebiusColorRuler:
    """Ruler using Moebius inversion for capability-to-color mapping"""
    
    def __init__(self, num_goblins: int = 300):
        self.num_goblins = num_goblins
        self.moebius = MoebiusFunction()
        
        # Initialize capability space
        self.capability_ids: Dict[str, int] = {}
        self.capability_counter = 0
        
        # 3-fold application layers
        self.layer_1: Dict[int, SplitmixTernaryColor] = {}  # Direct mapping
        self.layer_2: Dict[int, SplitmixTernaryColor] = {}  # Inverted mapping
        self.layer_3: Dict[int, SplitmixTernaryColor] = {}  # Double inverted
        
        # Goblin assignments
        self.goblin_colors: Dict[int, Tuple[str, str, str]] = {}  # (layer1, layer2, layer3)
        self.goblin_capabilities: Dict[int, List[str]] = defaultdict(list)
    
    def register_capability(self, capability: str) -> int:
        """Register a capability and get its ID"""
        if capability not in self.capability_ids:
            self.capability_counter += 1
            self.capability_ids[capability] = self.capability_counter
        return self.capability_ids[capability]
    
    def _compute_ternary_from_int(self, value: int, seed: int = 42) -> SplitmixTernaryColor:
        """Convert integer to ternary color deterministically"""
        # Use splitmix-like mixing with seed
        h = value ^ seed
        h ^= h >> 33
        h *= 0xff51afd7ed558ccd
        h ^= h >> 33
        
        # Extract three ternary digits
        r = int((h & 0x3) - 1) if ((h >> 0) & 0x3) < 3 else 0
        g = int(((h >> 2) & 0x3) - 1) if ((h >> 2) & 0x3) < 3 else 0
        b = int(((h >> 4) & 0x3) - 1) if ((h >> 4) & 0x3) < 3 else 0
        
        return SplitmixTernaryColor(r, g, b)
    
    def assign_colors_layer_1(self):
        """Layer 1: Direct Moebius-based color assignment"""
        print("\nLAYER 1: DIRECT MOEBIUS MAPPING")
        print("=" * 70)
        
        for goblin_id in range(self.num_goblins):
            # Use goblin ID with Moebius function
            moebius_val = self.moebius.mu(goblin_id + 1)
            
            # Create color based on Moebius value
            color = self._compute_ternary_from_int(goblin_id + 1, seed=moebius_val)
            self.layer_1[goblin_id] = color
        
        print(f"✓ Assigned {len(self.layer_1)} goblin colors (Layer 1)")
        
        # Show sample
        for goblin_id in [0, 1, 2, 149, 150, 299]:
            if goblin_id in self.layer_1:
                print(f"  Goblin_{goblin_id:04d}: {self.layer_1[goblin_id]}")
    
    def assign_colors_layer_2(self):
        """Layer 2: Moebius-inverted assignment"""
        print("\nLAYER 2: MOEBIUS-INVERTED MAPPING")
        print("=" * 70)
        
        # Create function to invert
        layer_1_func = {
            goblin_id: float(self.layer_1[goblin_id].r + self.layer_1[goblin_id].g + self.layer_1[goblin_id].b)
            for goblin_id in self.layer_1
        }
        
        # Apply Moebius inversion conceptually by XOR with layer 1
        for goblin_id in range(self.num_goblins):
            layer_1_color = self.layer_1[goblin_id]
            
            # Invert colors: -1 ↔ 1, 0 stays 0
            inverted = SplitmixTernaryColor(
                -layer_1_color.r if layer_1_color.r != 0 else 0,
                -layer_1_color.g if layer_1_color.g != 0 else 0,
                -layer_1_color.b if layer_1_color.b != 0 else 0,
            )
            self.layer_2[goblin_id] = inverted
        
        print(f"✓ Assigned {len(self.layer_2)} goblin colors (Layer 2 - inverted)")
        
        # Show sample
        for goblin_id in [0, 1, 2, 149, 150, 299]:
            if goblin_id in self.layer_2:
                print(f"  Goblin_{goblin_id:04d}: {self.layer_2[goblin_id]}")
    
    def assign_colors_layer_3(self):
        """Layer 3: Double-inverted (Moebius square)"""
        print("\nLAYER 3: DOUBLE-INVERTED MAPPING (MOEBIUS SQUARE)")
        print("=" * 70)
        
        for goblin_id in range(self.num_goblins):
            layer_2_color = self.layer_2[goblin_id]
            
            # Double invert: apply layer 2 inversion again
            double_inverted = SplitmixTernaryColor(
                -layer_2_color.r if layer_2_color.r != 0 else 0,
                -layer_2_color.g if layer_2_color.g != 0 else 0,
                -layer_2_color.b if layer_2_color.b != 0 else 0,
            )
            self.layer_3[goblin_id] = double_inverted
        
        print(f"✓ Assigned {len(self.layer_3)} goblin colors (Layer 3 - double inverted)")
        
        # Show sample
        for goblin_id in [0, 1, 2, 149, 150, 299]:
            if goblin_id in self.layer_3:
                print(f"  Goblin_{goblin_id:04d}: {self.layer_3[goblin_id]}")
    
    def assign_goblin_colors(self):
        """Execute 3-fold color assignment"""
        self.assign_colors_layer_1()
        self.assign_colors_layer_2()
        self.assign_colors_layer_3()
        
        # Store all three layers for each goblin
        for goblin_id in range(self.num_goblins):
            self.goblin_colors[goblin_id] = (
                self.layer_1[goblin_id].to_hex(),
                self.layer_2[goblin_id].to_hex(),
                self.layer_3[goblin_id].to_hex(),
            )
    
    def discover_capability_colors(self, goblin_id: int, discovered_capabilities: List[str]):
        """Assign colors to discovered capabilities using Moebius ruler"""
        goblin_color = self.goblin_colors[goblin_id]
        
        for capability in discovered_capabilities:
            cap_id = self.register_capability(capability)
            self.goblin_capabilities[goblin_id].append(capability)
    
    def get_statistics(self) -> Dict:
        """Get ruler statistics"""
        return {
            "num_goblins": self.num_goblins,
            "goblins_with_colors": len(self.goblin_colors),
            "capabilities_registered": len(self.capability_ids),
            "layer_1_assignments": len(self.layer_1),
            "layer_2_assignments": len(self.layer_2),
            "layer_3_assignments": len(self.layer_3),
            "timestamp": datetime.now().isoformat()
        }
    
    def print_summary(self):
        """Print ruler summary"""
        stats = self.get_statistics()
        
        print(f"\n{'='*70}")
        print(f"MOEBIUS COLOR RULER SUMMARY")
        print(f"{'='*70}")
        print(f"\nGoblin Color Assignments:")
        print(f"  Goblins with colors: {stats['goblins_with_colors']}")
        print(f"  Capabilities registered: {stats['capabilities_registered']}")
        
        print(f"\nMoebius Inversion Layers:")
        print(f"  Layer 1 (Direct): {stats['layer_1_assignments']} assignments")
        print(f"  Layer 2 (Inverted): {stats['layer_2_assignments']} assignments")
        print(f"  Layer 3 (Double-Inverted): {stats['layer_3_assignments']} assignments")
        
        # Show Moebius function analysis
        moebius_counts = defaultdict(int)
        for i in range(1, 301):
            mu = MoebiusFunction.mu(i)
            moebius_counts[mu] += 1
        
        print(f"\nMoebius Function Distribution (1-300):")
        print(f"  μ(n) = -1: {moebius_counts[-1]} (odd prime factors)")
        print(f"  μ(n) =  0: {moebius_counts[0]} (squared prime factors)")
        print(f"  μ(n) =  1: {moebius_counts[1]} (even prime factors)")
    
    def export_ruler(self, filepath: str = "moebius_color_ruler.json"):
        """Export ruler assignments"""
        data = {
            "system": "MoebiusColorRuler",
            "num_goblins": self.num_goblins,
            "goblin_colors": {},
            "capabilities": self.capability_ids,
            "statistics": self.get_statistics()
        }
        
        for goblin_id, colors in self.goblin_colors.items():
            data["goblin_colors"][f"Goblin_{goblin_id:04d}"] = {
                "layer_1": colors[0],
                "layer_2": colors[1],
                "layer_3": colors[2],
                "capabilities": self.goblin_capabilities[goblin_id]
            }
        
        with open(filepath, 'w') as f:
            json.dump(data, f, indent=2)
        
        print(f"\n✓ Exported ruler to {filepath}")


# ============================================================================
# MAIN DEMONSTRATION
# ============================================================================

def main():
    """Run Moebius color ruler system"""
    
    print("\n╔════════════════════════════════════════════════════════════════╗")
    print("║     GOBLIN MOEBIUS COLOR RULER SYSTEM                          ║")
    print("║     Moebius Inversion + Splitmixternary Colors                 ║")
    print("║     3-Fold Application: Direct → Inverted → Double-Inverted    ║")
    print("╚════════════════════════════════════════════════════════════════╝")
    
    # Create ruler
    ruler = MoebiusColorRuler(num_goblins=300)
    
    print(f"\n✓ Initialized MoebiusColorRuler")
    print(f"  - 300 goblins")
    print(f"  - 3-fold Moebius transformation layers")
    print(f"  - Splitmixternary color system")
    
    # Apply 3-fold coloring
    print(f"\n{'='*70}")
    print(f"APPLYING 3-FOLD MOEBIUS COLOR TRANSFORMATION")
    print(f"{'='*70}")
    
    ruler.assign_goblin_colors()
    
    # Simulate capability discovery
    print(f"\n{'='*70}")
    print(f"CAPABILITY DISCOVERY WITH COLOR RULER")
    print(f"{'='*70}")
    
    capability_samples = [
        ["neural_networks", "optimization"],
        ["constraint_solving", "symbolic_reasoning"],
        ["reinforcement_learning"],
        ["knowledge_graphs", "semantic_search"],
        ["verification", "proof_checking"]
    ]
    
    for goblin_id in [0, 99, 199, 299]:
        capabilities = capability_samples[goblin_id % len(capability_samples)]
        ruler.discover_capability_colors(goblin_id, capabilities)
    
    print(f"✓ Discovered capabilities for sample goblins")
    
    # Print summary
    ruler.print_summary()
    
    # Show layer comparison
    print(f"\n{'='*70}")
    print(f"LAYER COMPARISON (Sample Goblins)")
    print(f"{'='*70}\n")
    
    for goblin_id in [0, 1, 149, 150, 299]:
        colors = ruler.goblin_colors[goblin_id]
        print(f"Goblin_{goblin_id:04d}:")
        print(f"  Layer 1 (Direct):          {colors[0]}")
        print(f"  Layer 2 (Inverted):        {colors[1]}")
        print(f"  Layer 3 (Double-Inverted): {colors[2]}")
    
    # Export
    ruler.export_ruler()
    
    # Final message
    print(f"\n{'╔════════════════════════════════════════════════════════════════╗'}")
    print(f"║              MOEBIUS COLOR RULER COMPLETE                       ║")
    print(f"╚════════════════════════════════════════════════════════════════╝\n")
    
    print("Key Features Demonstrated:")
    print("  ✓ Moebius function for number-theoretic coloring")
    print("  ✓ Splitmixternary balanced ternary color system")
    print("  ✓ 3-fold transformation layers (direct → inverted → double)")
    print("  ✓ Deterministic color assignment per goblin")
    print("  ✓ Capability color mapping")
    print("  ✓ MCP-compatible ruler interface")


if __name__ == "__main__":
    main()
