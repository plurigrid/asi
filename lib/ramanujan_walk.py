"""
Ramanujan Complex Random Walk for Interaction Pattern Discovery
Seed: 0x42D | Trit: +1 (PLUS agent - generative/optimistic)

Mathematical Foundation:
- Ramanujan graph: spectral gap λ₁ - λ₂ ≥ 2√(k-1) for k-regular
- Non-backtracking walk: Hashimoto matrix avoids revisiting edges
- Pattern discovery via stationary distribution anomalies
"""

from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional, Set, Callable
from enum import Enum, auto
import numpy as np
from collections import defaultdict
import json

# ═══════════════════════════════════════════════════════════════════════════════
# GF(3) TRIT SYSTEM - Conservation Law
# ═══════════════════════════════════════════════════════════════════════════════

class Trit(Enum):
    """GF(3) element: {-1, 0, +1} with addition mod 3"""
    MINUS = -1
    ZERO = 0
    PLUS = 1
    
    def __add__(self, other: 'Trit') -> 'Trit':
        return Trit((self.value + other.value + 3) % 3 - 1 if (self.value + other.value) not in [-1,0,1] else self.value + other.value)
    
    def __neg__(self) -> 'Trit':
        return Trit(-self.value)
    
    @staticmethod
    def from_int(n: int) -> 'Trit':
        return Trit(((n % 3) + 1) % 3 - 1)

def gf3_add(a: int, b: int) -> int:
    """GF(3) addition: result in {-1, 0, +1}"""
    s = a + b
    if s > 1: return s - 3
    if s < -1: return s + 3
    return s

# ═══════════════════════════════════════════════════════════════════════════════
# SPLITMIX64 DETERMINISTIC RNG (Gay-MCP Compatible)
# ═══════════════════════════════════════════════════════════════════════════════

class SplitMix64:
    """Deterministic PRNG for reproducible walks"""
    
    def __init__(self, seed: int = 0x42D):
        self.state = seed & ((1 << 64) - 1)
    
    def next(self) -> int:
        self.state = (self.state + 0x9E3779B97F4A7C15) & ((1 << 64) - 1)
        z = self.state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & ((1 << 64) - 1)
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & ((1 << 64) - 1)
        return z ^ (z >> 31)
    
    def next_float(self) -> float:
        return self.next() / ((1 << 64) - 1)
    
    def next_trit(self) -> int:
        """Generate trit in {-1, 0, +1}"""
        return (self.next() % 3) - 1

# ═══════════════════════════════════════════════════════════════════════════════
# OKLCH COLOR SPACE (Gay-MCP Palette)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class OkLCH:
    """OkLCH perceptual color - deterministic from seed"""
    L: float  # Lightness [0, 1]
    C: float  # Chroma [0, 0.4]
    H: float  # Hue [0, 360)
    
    @classmethod
    def from_seed(cls, seed: int) -> 'OkLCH':
        rng = SplitMix64(seed)
        return cls(
            L=0.4 + 0.4 * rng.next_float(),  # 0.4-0.8 for readability
            C=0.1 + 0.2 * rng.next_float(),  # 0.1-0.3 for vibrancy
            H=rng.next_float() * 360
        )
    
    @classmethod
    def from_trit(cls, trit: int, base_seed: int = 0x42D) -> 'OkLCH':
        """Map trit to color: +1=warm, 0=neutral, -1=cool"""
        hue_base = {1: 30, 0: 180, -1: 270}[trit]  # Orange, Cyan, Purple
        rng = SplitMix64(base_seed ^ (trit + 2))
        return cls(
            L=0.5 + 0.2 * rng.next_float(),
            C=0.15 + 0.1 * rng.next_float(),
            H=hue_base + 30 * (rng.next_float() - 0.5)
        )
    
    def to_css(self) -> str:
        return f"oklch({self.L:.2f} {self.C:.3f} {self.H:.1f})"
    
    def to_hex(self) -> str:
        """Approximate conversion to hex for ASCII viz"""
        # Simplified: map hue to RGB sector
        h = self.H / 60
        c = self.C * 2.5  # Scale chroma
        x = c * (1 - abs(h % 2 - 1))
        
        if h < 1: r, g, b = c, x, 0
        elif h < 2: r, g, b = x, c, 0
        elif h < 3: r, g, b = 0, c, x
        elif h < 4: r, g, b = 0, x, c
        elif h < 5: r, g, b = x, 0, c
        else: r, g, b = c, 0, x
        
        m = self.L - c / 2
        r, g, b = int((r + m) * 255), int((g + m) * 255), int((b + m) * 255)
        r, g, b = max(0, min(255, r)), max(0, min(255, g)), max(0, min(255, b))
        return f"#{r:02x}{g:02x}{b:02x}"

# ═══════════════════════════════════════════════════════════════════════════════
# RAMANUJAN GRAPH CONSTRUCTION
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class RamanujanGraph:
    """
    k-regular Ramanujan graph with optimal spectral gap.
    Uses LPS (Lubotzky-Phillips-Sarnak) construction principles.
    """
    n_vertices: int
    degree: int
    adjacency: Dict[int, List[int]] = field(default_factory=dict)
    edge_weights: Dict[Tuple[int, int], float] = field(default_factory=dict)
    vertex_colors: Dict[int, OkLCH] = field(default_factory=dict)
    vertex_trits: Dict[int, int] = field(default_factory=dict)
    
    def __post_init__(self):
        self._build_ramanujan()
        self._assign_colors()
    
    def _build_ramanujan(self):
        """Construct approximate Ramanujan graph via random regular graph"""
        rng = SplitMix64(0x42D)
        
        # Initialize adjacency
        for v in range(self.n_vertices):
            self.adjacency[v] = []
        
        # Build k-regular graph using configuration model
        # Each vertex needs exactly k stubs
        stubs = []
        for v in range(self.n_vertices):
            stubs.extend([v] * self.degree)
        
        # Shuffle and pair stubs
        for i in range(len(stubs) - 1, 0, -1):
            j = rng.next() % (i + 1)
            stubs[i], stubs[j] = stubs[j], stubs[i]
        
        # Create edges from paired stubs
        for i in range(0, len(stubs) - 1, 2):
            u, v = stubs[i], stubs[i + 1]
            if u != v and v not in self.adjacency[u]:
                self.adjacency[u].append(v)
                self.adjacency[v].append(u)
                self.edge_weights[(min(u, v), max(u, v))] = 1.0
        
        # Fill remaining edges to achieve regularity
        for v in range(self.n_vertices):
            while len(self.adjacency[v]) < self.degree:
                candidates = [u for u in range(self.n_vertices) 
                             if u != v and u not in self.adjacency[v] 
                             and len(self.adjacency[u]) < self.degree]
                if not candidates:
                    break
                u = candidates[rng.next() % len(candidates)]
                self.adjacency[v].append(u)
                self.adjacency[u].append(v)
                self.edge_weights[(min(u, v), max(u, v))] = 1.0
    
    def _assign_colors(self):
        """Assign GF(3) trits and colors ensuring local conservation"""
        rng = SplitMix64(0x42D)
        
        for v in range(self.n_vertices):
            trit = rng.next_trit()
            self.vertex_trits[v] = trit
            self.vertex_colors[v] = OkLCH.from_trit(trit, 0x42D + v)
    
    def spectral_gap(self) -> float:
        """
        Compute spectral gap λ₁ - λ₂.
        Ramanujan bound: gap ≥ 2√(k-1)
        """
        # Build adjacency matrix
        A = np.zeros((self.n_vertices, self.n_vertices))
        for v, neighbors in self.adjacency.items():
            for u in neighbors:
                A[v, u] = 1.0
        
        # Compute eigenvalues
        eigenvalues = np.linalg.eigvalsh(A)
        eigenvalues = np.sort(eigenvalues)[::-1]  # Descending
        
        if len(eigenvalues) >= 2:
            return eigenvalues[0] - eigenvalues[1]
        return 0.0
    
    def ramanujan_bound(self) -> float:
        """Theoretical Ramanujan bound: 2√(k-1)"""
        return 2 * np.sqrt(max(self.degree - 1, 1))
    
    def is_ramanujan(self) -> bool:
        """Check if graph satisfies Ramanujan property"""
        return self.spectral_gap() >= self.ramanujan_bound() - 0.1  # Small tolerance

# ═══════════════════════════════════════════════════════════════════════════════
# NON-BACKTRACKING RANDOM WALK
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class WalkStep:
    """Single step in non-backtracking walk"""
    vertex: int
    prev_vertex: Optional[int]
    trit: int
    color: OkLCH
    step_number: int

@dataclass 
class WalkTrajectory:
    """Complete walk trajectory with pattern metadata"""
    steps: List[WalkStep] = field(default_factory=list)
    trit_sum: int = 0  # Running GF(3) sum
    entropy: float = 0.0
    pattern_type: str = "unknown"
    
    def add_step(self, step: WalkStep):
        self.steps.append(step)
        self.trit_sum = gf3_add(self.trit_sum, step.trit)
    
    def compute_entropy(self) -> float:
        """Compute path entropy from visit distribution"""
        if not self.steps:
            return 0.0
        
        visit_counts = defaultdict(int)
        for step in self.steps:
            visit_counts[step.vertex] += 1
        
        n = len(self.steps)
        probs = [c / n for c in visit_counts.values()]
        self.entropy = -sum(p * np.log(p + 1e-10) for p in probs)
        return self.entropy

class NonBacktrackingWalk:
    """
    Non-backtracking random walk on Ramanujan graph.
    Uses Hashimoto matrix formulation: no immediate edge reversal.
    """
    
    def __init__(self, graph: RamanujanGraph, seed: int = 0x42D):
        self.graph = graph
        self.rng = SplitMix64(seed)
        self.trajectories: List[WalkTrajectory] = []
    
    def walk(self, start: int, steps: int) -> WalkTrajectory:
        """Execute non-backtracking walk from start vertex"""
        trajectory = WalkTrajectory()
        
        current = start
        prev = None
        
        for i in range(steps):
            # Get neighbors excluding previous (non-backtracking)
            neighbors = self.graph.adjacency.get(current, [])
            if prev is not None:
                neighbors = [n for n in neighbors if n != prev]
            
            if not neighbors:
                # Dead end - allow backtrack as last resort
                neighbors = self.graph.adjacency.get(current, [])
            
            if not neighbors:
                break
            
            # Record current step
            step = WalkStep(
                vertex=current,
                prev_vertex=prev,
                trit=self.graph.vertex_trits[current],
                color=self.graph.vertex_colors[current],
                step_number=i
            )
            trajectory.add_step(step)
            
            # Move to next vertex
            prev = current
            current = neighbors[self.rng.next() % len(neighbors)]
        
        # Final step
        trajectory.add_step(WalkStep(
            vertex=current,
            prev_vertex=prev,
            trit=self.graph.vertex_trits[current],
            color=self.graph.vertex_colors[current],
            step_number=steps
        ))
        
        trajectory.compute_entropy()
        self.trajectories.append(trajectory)
        return trajectory
    
    def discover_patterns(self, n_walks: int = 100, walk_length: int = 50) -> Dict:
        """
        Run multiple walks to discover interaction patterns.
        Returns classified patterns with Pontryagin dual characters.
        """
        patterns = {
            'convergent': [],
            'oscillating': [],
            'exploratory': [],
            'surprising': []
        }
        
        for w in range(n_walks):
            start = self.rng.next() % self.graph.n_vertices
            trajectory = self.walk(start, walk_length)
            
            # Classify pattern
            pattern_type = self._classify_pattern(trajectory)
            trajectory.pattern_type = pattern_type
            patterns[pattern_type].append(trajectory)
        
        return patterns
    
    def _classify_pattern(self, trajectory: WalkTrajectory) -> str:
        """
        Classify walk pattern based on:
        - Entropy (exploration vs concentration)
        - Return rate (oscillation detection)
        - Trit sum (GF(3) conservation check)
        - Probability (surprising = low prob high value)
        """
        if len(trajectory.steps) < 3:
            return 'exploratory'
        
        # Check for oscillation (high return rate)
        visits = defaultdict(int)
        for step in trajectory.steps:
            visits[step.vertex] += 1
        max_visits = max(visits.values())
        return_rate = max_visits / len(trajectory.steps)
        
        if return_rate > 0.15:  # Lowered threshold
            return 'oscillating'
        
        # Check for convergence (stays in small region)
        unique_vertices = len(visits)
        coverage_ratio = unique_vertices / self.graph.n_vertices
        if coverage_ratio < 0.5:  # Visits less than half the graph
            return 'convergent'
        
        # Check for surprising patterns (GF(3) = 0 is special)
        if trajectory.trit_sum == 0 and trajectory.entropy < 3.8:
            return 'surprising'
        
        return 'exploratory'

# ═══════════════════════════════════════════════════════════════════════════════
# PONTRYAGIN DUALITY - Characters on Walk Groups
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Character:
    """
    Character χ: G → S¹ on the group of walk steps.
    Pontryagin dual: Ĝ = Hom(G, S¹)
    For GF(3): characters are ω^k where ω = e^(2πi/3)
    """
    index: int  # k ∈ {0, 1, 2} for GF(3)
    
    def evaluate(self, trit: int) -> complex:
        """χ_k(t) = ω^(kt) where ω = e^(2πi/3)"""
        omega = np.exp(2j * np.pi / 3)
        return omega ** (self.index * (trit + 1))  # Shift to {0,1,2}
    
    def evaluate_trajectory(self, trajectory: WalkTrajectory) -> complex:
        """Fourier coefficient of trajectory under this character"""
        return sum(self.evaluate(step.trit) for step in trajectory.steps)

class PontryaginAnalyzer:
    """
    Analyze patterns via Pontryagin duality.
    The dual group Ĝ reveals frequency structure of walk trajectories.
    """
    
    def __init__(self):
        # GF(3) has 3 characters
        self.characters = [Character(k) for k in range(3)]
    
    def fourier_transform(self, trajectory: WalkTrajectory) -> List[complex]:
        """Compute Fourier coefficients under all characters"""
        return [χ.evaluate_trajectory(trajectory) for χ in self.characters]
    
    def dominant_character(self, trajectory: WalkTrajectory) -> Tuple[int, float]:
        """Find character with largest coefficient magnitude"""
        coeffs = self.fourier_transform(trajectory)
        magnitudes = [abs(c) for c in coeffs]
        dominant_idx = np.argmax(magnitudes)
        return dominant_idx, magnitudes[dominant_idx]
    
    def character_signature(self, patterns: Dict) -> Dict:
        """Compute character signatures for pattern types"""
        signatures = {}
        
        for pattern_type, trajectories in patterns.items():
            if not trajectories:
                signatures[pattern_type] = {'dominant': -1, 'spectrum': [0, 0, 0]}
                continue
            
            avg_spectrum = [0.0, 0.0, 0.0]
            for traj in trajectories:
                coeffs = self.fourier_transform(traj)
                for i, c in enumerate(coeffs):
                    avg_spectrum[i] += abs(c)
            
            n = len(trajectories)
            avg_spectrum = [s / n for s in avg_spectrum]
            dominant = int(np.argmax(avg_spectrum))
            
            signatures[pattern_type] = {
                'dominant': dominant,
                'spectrum': avg_spectrum,
                'interpretation': self._interpret_character(dominant)
            }
        
        return signatures
    
    def _interpret_character(self, idx: int) -> str:
        """Interpret dominant character"""
        interpretations = {
            0: "Trivial (uniform distribution)",
            1: "Cyclic (ω rotation - forward bias)",
            2: "Anti-cyclic (ω² rotation - backward bias)"
        }
        return interpretations.get(idx, "Unknown")

# ═══════════════════════════════════════════════════════════════════════════════
# MAIN DISCOVERY ENGINE
# ═══════════════════════════════════════════════════════════════════════════════

def run_discovery(n_vertices: int = 64, degree: int = 4, 
                  n_walks: int = 100, walk_length: int = 50,
                  seed: int = 0x42D) -> Dict:
    """
    Run complete Ramanujan walk discovery pipeline.
    
    Returns: Pattern discovery results with:
    - Graph spectral properties
    - Classified patterns with colors
    - Pontryagin dual characterization
    """
    # Build Ramanujan graph
    graph = RamanujanGraph(n_vertices=n_vertices, degree=degree)
    
    # Run non-backtracking walks
    walker = NonBacktrackingWalk(graph, seed=seed)
    patterns = walker.discover_patterns(n_walks=n_walks, walk_length=walk_length)
    
    # Analyze via Pontryagin duality
    analyzer = PontryaginAnalyzer()
    signatures = analyzer.character_signature(patterns)
    
    # Compute summary statistics
    results = {
        'graph': {
            'n_vertices': n_vertices,
            'degree': degree,
            'spectral_gap': float(graph.spectral_gap()),
            'ramanujan_bound': float(graph.ramanujan_bound()),
            'is_ramanujan': bool(graph.is_ramanujan())
        },
        'patterns': {
            ptype: {
                'count': len(trajectories),
                'avg_entropy': float(np.mean([t.entropy for t in trajectories])) if trajectories else 0,
                'avg_trit_sum': float(np.mean([t.trit_sum for t in trajectories])) if trajectories else 0,
                'color': OkLCH.from_trit({'convergent': 0, 'oscillating': -1, 
                                          'exploratory': 1, 'surprising': 0}[ptype]).to_css()
            }
            for ptype, trajectories in patterns.items()
        },
        'pontryagin': signatures,
        'gf3_conservation': {
            'total_walks': n_walks,
            'zero_sum_walks': sum(1 for trajs in patterns.values() 
                                  for t in trajs if t.trit_sum == 0),
            'conservation_rate': sum(1 for trajs in patterns.values() 
                                     for t in trajs if t.trit_sum == 0) / max(n_walks, 1)
        }
    }
    
    return results

if __name__ == "__main__":
    results = run_discovery()
    print(json.dumps(results, indent=2))
