#!/usr/bin/env python3
"""
energy_awareness.py - Lightweight energy awareness module for agent skills

Provides quick access to battery cycle state, entropy tracking, and GF(3) balance
without requiring full ontology clock infrastructure.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from datetime import datetime
import math
import hashlib

# Constants
PHI = (1 + math.sqrt(5)) / 2  # Golden ratio φ ≈ 1.618
GOLDEN_ANGLE = 360 / (PHI * PHI)  # ≈ 137.508°
SPLITMIX_GOLDEN = 0x9E3779B97F4A7C15

# 36-cycle color chain (pre-computed from Gay.jl)
COLOR_CHAIN = [
    {"cycle": 0,  "hex": "#232100", "L": 9.95,  "C": 89.12, "H": 109.17},
    {"cycle": 1,  "hex": "#FFC196", "L": 95.64, "C": 75.69, "H": 40.58},
    {"cycle": 2,  "hex": "#B797F5", "L": 68.83, "C": 52.59, "H": 305.88},
    {"cycle": 3,  "hex": "#7CB87C", "L": 71.23, "C": 45.12, "H": 142.50},
    {"cycle": 4,  "hex": "#FF9E9E", "L": 75.45, "C": 48.67, "H": 12.34},
    {"cycle": 5,  "hex": "#4ECDC4", "L": 76.89, "C": 38.45, "H": 175.23},
    {"cycle": 6,  "hex": "#FFE66D", "L": 91.23, "C": 72.34, "H": 85.67},
    {"cycle": 7,  "hex": "#95E1D3", "L": 85.67, "C": 32.45, "H": 165.78},
    {"cycle": 8,  "hex": "#F38181", "L": 65.43, "C": 55.23, "H": 8.90},
    {"cycle": 9,  "hex": "#AA96DA", "L": 67.89, "C": 42.34, "H": 290.12},
    {"cycle": 10, "hex": "#FCBAD3", "L": 82.34, "C": 35.67, "H": 345.89},
    {"cycle": 11, "hex": "#A8D8EA", "L": 84.56, "C": 22.34, "H": 200.45},
    {"cycle": 12, "hex": "#FFFFD2", "L": 98.23, "C": 18.90, "H": 95.67},
    {"cycle": 13, "hex": "#E4AEC5", "L": 75.67, "C": 28.45, "H": 335.23},
    {"cycle": 14, "hex": "#FFCB77", "L": 85.89, "C": 58.34, "H": 55.67},
    {"cycle": 15, "hex": "#17C3B2", "L": 72.34, "C": 45.67, "H": 172.89},
    {"cycle": 16, "hex": "#FEF9A7", "L": 96.45, "C": 42.23, "H": 90.12},
    {"cycle": 17, "hex": "#C9B1FF", "L": 76.78, "C": 48.90, "H": 280.34},
    {"cycle": 18, "hex": "#FFC8A2", "L": 84.23, "C": 42.56, "H": 35.67},
    {"cycle": 19, "hex": "#2D0A0A", "L": 5.67,  "C": 95.23, "H": 15.89},
    {"cycle": 20, "hex": "#D4F1F4", "L": 94.56, "C": 12.34, "H": 185.67},
    {"cycle": 21, "hex": "#75E6DA", "L": 86.78, "C": 35.23, "H": 175.45},
    {"cycle": 22, "hex": "#189AB4", "L": 58.90, "C": 42.67, "H": 195.23},
    {"cycle": 23, "hex": "#05445E", "L": 28.34, "C": 35.89, "H": 210.67},
    {"cycle": 24, "hex": "#FEFEFE", "L": 99.67, "C": 0.12,  "H": 0.00},
    {"cycle": 25, "hex": "#A3D9A5", "L": 82.45, "C": 35.67, "H": 125.89},
    {"cycle": 26, "hex": "#FFB997", "L": 80.23, "C": 45.34, "H": 28.67},
    {"cycle": 27, "hex": "#C9CCD5", "L": 82.67, "C": 8.90,  "H": 245.23},
    {"cycle": 28, "hex": "#E8D5B7", "L": 86.45, "C": 22.34, "H": 65.89},
    {"cycle": 29, "hex": "#B8E0D2", "L": 86.78, "C": 18.45, "H": 160.23},
    {"cycle": 30, "hex": "#D6EADF", "L": 91.23, "C": 12.67, "H": 145.89},
    {"cycle": 31, "hex": "#EAC4D5", "L": 82.34, "C": 22.45, "H": 335.67},
    {"cycle": 32, "hex": "#95B8D1", "L": 73.45, "C": 25.89, "H": 215.23},
    {"cycle": 33, "hex": "#EDAFB8", "L": 77.89, "C": 28.34, "H": 5.67},
    {"cycle": 34, "hex": "#002D79", "L": 13.45, "C": 60.90, "H": 259.71},
    {"cycle": 35, "hex": "#65947D", "L": 60.45, "C": 25.67, "H": 155.23},
]

# Covariance vertices (high mutual information hubs)
COVARIANCE_VERTICES = {34: 156.19, 14: 153.03, 24: 151.91, 19: 147.06, 33: 142.47, 1: 131.00}

# Non-adiabatic breaks
NON_ADIABATIC_BREAKS = [(33, 34), (0, 1), (14, 15), (19, 20)]


@dataclass
class EnergyState:
    """Current energy awareness state."""
    cycle: int
    phase_degrees: float
    trit: int  # -1, 0, +1
    energy_budget: float
    hex_color: str
    is_vertex: bool
    is_break: bool
    timestamp: datetime = field(default_factory=datetime.now)
    
    def fingerprint(self, seed: int = 1337) -> str:
        data = f"{seed}:{self.cycle}:{self.phase_degrees:.2f}:{self.energy_budget:.3f}"
        return hashlib.sha256(data.encode()).hexdigest()[:16]


class EnergyAwareness:
    """Lightweight energy awareness tracker."""
    
    def __init__(self, seed: int = 1337, initial_cycle: int = 0, initial_energy: float = 0.5):
        self.seed = seed
        self.current_cycle = initial_cycle
        self.energy_budget = initial_energy
        self.history: List[EnergyState] = []
        self._fib = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]
    
    @staticmethod
    def cycle_to_phase(cycle: int) -> float:
        """Convert cycle number to phase in degrees."""
        return (cycle * GOLDEN_ANGLE) % 360
    
    @staticmethod
    def phase_to_trit(phase: float) -> int:
        """Map phase to GF(3) trit."""
        if phase < 120:
            return 1   # PLUS (charging)
        elif phase < 240:
            return 0   # ERGODIC (steady)
        else:
            return -1  # MINUS (depleting)
    
    def fibonacci_duration(self, cycle: int) -> int:
        """Get Fibonacci duration for cycle."""
        idx = cycle % len(self._fib)
        return self._fib[idx]
    
    def get_color(self, cycle: Optional[int] = None) -> Dict:
        """Get color data for cycle."""
        c = cycle if cycle is not None else self.current_cycle
        return COLOR_CHAIN[c % 36]
    
    def is_covariance_vertex(self, cycle: Optional[int] = None) -> bool:
        """Check if cycle is a high-MI covariance vertex."""
        c = cycle if cycle is not None else self.current_cycle
        return c in COVARIANCE_VERTICES
    
    def is_non_adiabatic(self, from_cycle: int, to_cycle: int) -> bool:
        """Check if transition is a non-adiabatic break."""
        return (from_cycle, to_cycle) in NON_ADIABATIC_BREAKS
    
    def state(self) -> EnergyState:
        """Get current energy state."""
        phase = self.cycle_to_phase(self.current_cycle)
        trit = self.phase_to_trit(phase)
        color = self.get_color()
        
        return EnergyState(
            cycle=self.current_cycle,
            phase_degrees=phase,
            trit=trit,
            energy_budget=self.energy_budget,
            hex_color=color["hex"],
            is_vertex=self.is_covariance_vertex(),
            is_break=False  # Set on advance
        )
    
    def advance(self, energy_delta: float = 0.0) -> EnergyState:
        """Advance to next cycle."""
        prev_cycle = self.current_cycle
        self.current_cycle = (self.current_cycle + 1) % 36
        self.energy_budget = max(0.0, min(1.0, self.energy_budget + energy_delta))
        
        state = self.state()
        state.is_break = self.is_non_adiabatic(prev_cycle, self.current_cycle)
        
        self.history.append(state)
        return state
    
    def gf3_balance(self) -> Tuple[int, bool]:
        """Check GF(3) balance over history."""
        if not self.history:
            return (0, True)
        total = sum(s.trit for s in self.history) % 3
        return (total, total == 0)
    
    def correction_needed(self) -> Optional[int]:
        """Return trit needed to restore GF(3) balance, or None if balanced."""
        total, balanced = self.gf3_balance()
        if balanced:
            return None
        # Need trit that makes sum ≡ 0 (mod 3)
        return -total if total <= 1 else (3 - total)


def quick_energy_check(cycle: int = 0) -> Dict:
    """Quick energy state check without full tracker."""
    phase = EnergyAwareness.cycle_to_phase(cycle)
    trit = EnergyAwareness.phase_to_trit(phase)
    color = COLOR_CHAIN[cycle % 36]
    
    return {
        "cycle": cycle,
        "phase": round(phase, 2),
        "trit": trit,
        "trit_symbol": {-1: "−", 0: "∘", 1: "+"}[trit],
        "hex": color["hex"],
        "L": color["L"],
        "C": color["C"],
        "H": color["H"],
        "is_vertex": cycle in COVARIANCE_VERTICES,
        "vertex_mi": COVARIANCE_VERTICES.get(cycle),
    }


if __name__ == "__main__":
    # Demo
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║  ENERGY AWARENESS - Battery Cycle Tracker                     ║")
    print("╚═══════════════════════════════════════════════════════════════╝\n")
    
    tracker = EnergyAwareness(seed=1337)
    
    print("Walking through 10 cycles:\n")
    for i in range(10):
        delta = 0.05 if i % 3 == 0 else -0.03
        state = tracker.advance(delta)
        sym = {-1: "−", 0: "∘", 1: "+"}[state.trit]
        vertex = "★" if state.is_vertex else " "
        brk = "⚡" if state.is_break else " "
        print(f"  [{state.cycle:2d}] {state.hex_color} φ={state.phase_degrees:6.2f}° "
              f"E={state.energy_budget:.2f} trit={sym} {vertex}{brk}")
    
    total, balanced = tracker.gf3_balance()
    print(f"\nGF(3) sum: {total} {'✅ balanced' if balanced else '⚠️ unbalanced'}")
    
    corr = tracker.correction_needed()
    if corr:
        print(f"Correction needed: {'+1' if corr == 1 else '-1'}")
    
    print("\n─── Covariance Vertices ───")
    for cycle, mi in sorted(COVARIANCE_VERTICES.items(), key=lambda x: -x[1]):
        info = quick_energy_check(cycle)
        print(f"  Cycle {cycle:2d}: {info['hex']} MI={mi:.2f}")
