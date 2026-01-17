#!/usr/bin/env python3
"""
string_diagram_walk.py - Random Walks on String Diagrams via ACSet

Combines:
- py-acset pattern from browser_history_acset.py
- Spectral random walk from spectral_random_walk.jl
- DisCoPy-style monoidal structure from world_discopy.py
- GF(3) conservation from ramanujan_walk.py

Mathematical Foundation:
- String diagrams = 2D graphical calculus for monoidal categories
- ACSet = Functor F: C^op → Set encoding the combinatorial structure
- Random walk = Markov chain on the diagram's underlying graph
- Mixing time τ ∝ 1/spectral_gap (Bumpus comprehension model)

Seed: 0x42D (1069) | Trit: ERGODIC (coordination/infrastructure)
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Any, Set
from enum import Enum
from collections import defaultdict
import numpy as np
import hashlib
import json

# ═══════════════════════════════════════════════════════════════════════════════
# GF(3) TRIT SYSTEM
# ═══════════════════════════════════════════════════════════════════════════════

class Trit(Enum):
    """GF(3) element: {-1, 0, +1} with addition mod 3"""
    MINUS = -1    # Validators, analysis, verification
    ERGODIC = 0   # Coordinators, infrastructure, balance
    PLUS = 1      # Generators, creation, synthesis
    
    def __add__(self, other: 'Trit') -> 'Trit':
        val = (self.value + other.value)
        if val > 1: val -= 3
        if val < -1: val += 3
        return Trit(val)
    
    def __neg__(self) -> 'Trit':
        return Trit(-self.value)


def gf3_add(a: int, b: int) -> int:
    """GF(3) addition: result in {-1, 0, +1}"""
    s = a + b
    if s > 1: return s - 3
    if s < -1: return s + 3
    return s


# ═══════════════════════════════════════════════════════════════════════════════
# SPLITMIX64 DETERMINISTIC RNG (Gay.jl compatible)
# ═══════════════════════════════════════════════════════════════════════════════

class SplitMix64:
    """Deterministic PRNG for reproducible walks. Same seed = same sequence."""
    
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
    
    def choice(self, items: list) -> Any:
        if not items:
            return None
        return items[self.next() % len(items)]


# ═══════════════════════════════════════════════════════════════════════════════
# STRING DIAGRAM ACSET SCHEMA
# ═══════════════════════════════════════════════════════════════════════════════

SCHEMA_STRING_DIAGRAM = {
    "objects": [
        "Ty",      # Types (objects in the monoidal category)
        "Wire",    # Wires carrying types between boxes
        "Box",     # Morphism boxes (operations)
        "Port",    # Input/output ports on boxes
    ],
    "morphisms": {
        # Structural morphisms
        "wire_type": ("Wire", "Ty"),         # Each wire has a type
        "port_box": ("Port", "Box"),         # Ports belong to boxes
        "port_wire": ("Port", "Wire"),       # Ports connect to wires
        # Composition structure
        "box_layer": ("Box", "Layer"),       # Optional: boxes in layers for sequential comp
    },
    "attributes": {
        "Ty": ["name", "trit"],
        "Wire": ["id", "direction"],         # direction: "in" | "out" | "internal"
        "Box": ["name", "trit", "layer"],    # layer for sequential ordering
        "Port": ["kind", "index"],           # kind: "input" | "output", index for ordering
    }
}


@dataclass
class StringDiagramACSet:
    """
    ACSet (Attributed C-Set) for String Diagrams.
    
    Implements the categorical database pattern:
    - Objects: Ty, Wire, Box, Port
    - Morphisms: wire_type, port_box, port_wire
    - Attributes: name, trit, kind, etc.
    
    Supports:
    - O(1) incident queries via morphism indices
    - Random walk traversal on underlying graph
    - GF(3) conservation tracking
    """
    schema: dict = field(default_factory=lambda: SCHEMA_STRING_DIAGRAM)
    parts: dict = field(default_factory=dict)
    subparts: dict = field(default_factory=dict)
    
    # Indices for efficient navigation (morphism inverses)
    _indices: dict = field(default_factory=dict)
    
    def __post_init__(self):
        # Initialize part storage for each object type
        for ob in self.schema["objects"]:
            self.parts[ob] = []
        
        # Initialize subpart storage for morphisms
        for morph in self.schema["morphisms"]:
            self.subparts[morph] = []
            self._indices[morph] = defaultdict(list)  # target → [sources]
        
        # Initialize subpart storage for attributes
        for ob, attrs in self.schema["attributes"].items():
            for attr in attrs:
                self.subparts[f"{ob}_{attr}"] = []
    
    def add_part(self, ob: str, **attrs) -> int:
        """Add a part (element) to an object type. Returns the index."""
        idx = len(self.parts[ob])
        self.parts[ob].append(idx)
        
        # Store attributes
        for attr in self.schema["attributes"].get(ob, []):
            val = attrs.get(attr)
            self.subparts[f"{ob}_{attr}"].append(val)
        
        return idx
    
    def set_subpart(self, morph: str, src: int, tgt: int):
        """Set a morphism value: morph[src] = tgt"""
        # Extend list if needed
        while len(self.subparts[morph]) <= src:
            self.subparts[morph].append(None)
        
        self.subparts[morph][src] = tgt
        
        # Update inverse index
        self._indices[morph][tgt].append(src)
    
    def nparts(self, ob: str) -> int:
        """Number of parts in an object type."""
        return len(self.parts[ob])
    
    def subpart(self, morph: str, src: int) -> Optional[int]:
        """Get morphism value: morph[src]"""
        if src < len(self.subparts[morph]):
            return self.subparts[morph][src]
        return None
    
    def incident(self, tgt: int, morph: str) -> List[int]:
        """Find all sources that map to target via morphism (inverse lookup)."""
        return self._indices[morph].get(tgt, [])
    
    def get_attr(self, ob: str, idx: int, attr: str) -> Any:
        """Get attribute value for a part."""
        key = f"{ob}_{attr}"
        if key in self.subparts and idx < len(self.subparts[key]):
            return self.subparts[key][idx]
        return None
    
    def set_attr(self, ob: str, idx: int, attr: str, val: Any):
        """Set attribute value for a part."""
        key = f"{ob}_{attr}"
        while len(self.subparts[key]) <= idx:
            self.subparts[key].append(None)
        self.subparts[key][idx] = val


# ═══════════════════════════════════════════════════════════════════════════════
# STRING DIAGRAM BUILDER
# ═══════════════════════════════════════════════════════════════════════════════

class StringDiagramBuilder:
    """
    Fluent builder for constructing string diagrams as ACSets.
    
    Usage:
        diagram = (StringDiagramBuilder()
            .add_type("A", trit=1)
            .add_type("B", trit=-1)
            .add_box("f", inputs=["A"], outputs=["B"], trit=0)
            .add_box("g", inputs=["B"], outputs=["A"], trit=0)
            .connect("f", 0, "g", 0)  # Connect f's output to g's input
            .build())
    """
    
    def __init__(self, seed: int = 0x42D):
        self.acset = StringDiagramACSet()
        self.rng = SplitMix64(seed)
        
        # Caches for name → index lookup
        self._type_cache: Dict[str, int] = {}
        self._box_cache: Dict[str, int] = {}
        self._wire_cache: Dict[str, int] = {}
        
        # Track ports for connection
        self._box_inputs: Dict[int, List[int]] = defaultdict(list)   # box → [input ports]
        self._box_outputs: Dict[int, List[int]] = defaultdict(list)  # box → [output ports]
    
    def add_type(self, name: str, trit: int = 0) -> 'StringDiagramBuilder':
        """Add a type (object in the monoidal category)."""
        if name not in self._type_cache:
            idx = self.acset.add_part("Ty", name=name, trit=trit)
            self._type_cache[name] = idx
        return self
    
    def add_box(self, name: str, inputs: List[str], outputs: List[str], 
                trit: int = 0, layer: int = 0) -> 'StringDiagramBuilder':
        """
        Add a morphism box with typed input/output ports.
        
        Args:
            name: Box name (unique identifier)
            inputs: List of type names for input ports
            outputs: List of type names for output ports
            trit: GF(3) grading
            layer: Sequential layer (for composition ordering)
        """
        # Ensure types exist
        for ty_name in inputs + outputs:
            self.add_type(ty_name)
        
        # Create box
        box_idx = self.acset.add_part("Box", name=name, trit=trit, layer=layer)
        self._box_cache[name] = box_idx
        
        # Create input ports and wires
        for i, ty_name in enumerate(inputs):
            ty_idx = self._type_cache[ty_name]
            
            # Create input wire
            wire_idx = self.acset.add_part("Wire", id=f"{name}_in_{i}", direction="in")
            self.acset.set_subpart("wire_type", wire_idx, ty_idx)
            
            # Create input port
            port_idx = self.acset.add_part("Port", kind="input", index=i)
            self.acset.set_subpart("port_box", port_idx, box_idx)
            self.acset.set_subpart("port_wire", port_idx, wire_idx)
            
            self._box_inputs[box_idx].append(port_idx)
        
        # Create output ports and wires
        for i, ty_name in enumerate(outputs):
            ty_idx = self._type_cache[ty_name]
            
            # Create output wire
            wire_idx = self.acset.add_part("Wire", id=f"{name}_out_{i}", direction="out")
            self.acset.set_subpart("wire_type", wire_idx, ty_idx)
            
            # Create output port
            port_idx = self.acset.add_part("Port", kind="output", index=i)
            self.acset.set_subpart("port_box", port_idx, box_idx)
            self.acset.set_subpart("port_wire", port_idx, wire_idx)
            
            self._box_outputs[box_idx].append(port_idx)
        
        return self
    
    def connect(self, from_box: str, from_port: int, 
                to_box: str, to_port: int) -> 'StringDiagramBuilder':
        """
        Connect output port of from_box to input port of to_box.
        This merges the wires (they become the same wire).
        """
        from_box_idx = self._box_cache[from_box]
        to_box_idx = self._box_cache[to_box]
        
        # Get the ports
        out_port = self._box_outputs[from_box_idx][from_port]
        in_port = self._box_inputs[to_box_idx][to_port]
        
        # Get the output wire (this becomes the shared wire)
        out_wire = self.acset.subpart("port_wire", out_port)
        
        # Update the input port to point to the same wire
        self.acset.set_subpart("port_wire", in_port, out_wire)
        
        # Mark wire as internal (not boundary)
        self.acset.set_attr("Wire", out_wire, "direction", "internal")
        
        return self
    
    def build(self) -> StringDiagramACSet:
        """Return the constructed ACSet."""
        return self.acset


# ═══════════════════════════════════════════════════════════════════════════════
# GRAPH EXTRACTION FROM ACSET
# ═══════════════════════════════════════════════════════════════════════════════

def extract_box_graph(acset: StringDiagramACSet) -> Tuple[np.ndarray, Dict[int, int]]:
    """
    Extract adjacency matrix from string diagram ACSet.
    
    Graph structure: Boxes are nodes, wires define edges.
    Two boxes are adjacent if they share a wire (via ports).
    
    Returns:
        adjacency: n×n numpy array
        box_to_idx: mapping from ACSet box index to matrix index
    """
    n_boxes = acset.nparts("Box")
    
    if n_boxes == 0:
        return np.array([[]]), {}
    
    # Build adjacency matrix
    adjacency = np.zeros((n_boxes, n_boxes))
    box_to_idx = {i: i for i in range(n_boxes)}
    
    # For each wire, find all boxes connected to it
    n_wires = acset.nparts("Wire")
    
    for wire_idx in range(n_wires):
        # Find all ports connected to this wire
        ports = acset.incident(wire_idx, "port_wire")
        
        # Find boxes for these ports
        boxes_on_wire = []
        for port_idx in ports:
            box_idx = acset.subpart("port_box", port_idx)
            if box_idx is not None:
                boxes_on_wire.append(box_idx)
        
        # Connect all pairs of boxes on this wire
        for i, box_i in enumerate(boxes_on_wire):
            for box_j in boxes_on_wire[i+1:]:
                adjacency[box_i, box_j] = 1.0
                adjacency[box_j, box_i] = 1.0
    
    return adjacency, box_to_idx


def compute_laplacian(adjacency: np.ndarray) -> np.ndarray:
    """Compute graph Laplacian: L = D - A"""
    degrees = np.sum(adjacency, axis=1)
    D = np.diag(degrees)
    return D - adjacency


def spectral_gap(adjacency: np.ndarray) -> float:
    """
    Compute spectral gap λ₂ - λ₁ of the Laplacian.
    
    For connected graphs, λ₁ = 0, so gap = λ₂.
    Higher gap → faster mixing → better random walk exploration.
    """
    if adjacency.size == 0:
        return 0.0
    
    L = compute_laplacian(adjacency)
    eigenvalues = np.linalg.eigvalsh(L)
    eigenvalues = np.sort(eigenvalues)
    
    if len(eigenvalues) >= 2:
        return float(eigenvalues[1] - eigenvalues[0])
    return 0.0


def estimate_mixing_time(gap: float, n_nodes: int) -> float:
    """
    Estimate random walk mixing time from spectral gap.
    
    Theory: τ_mix ≈ log(n) / gap
    """
    if gap <= 1e-10:
        return float('inf')
    return np.log(n_nodes) / gap


# ═══════════════════════════════════════════════════════════════════════════════
# RANDOM WALK ON STRING DIAGRAM
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class WalkStep:
    """Single step in a random walk."""
    box_idx: int
    box_name: str
    trit: int
    step_number: int
    via_wire: Optional[int] = None


@dataclass 
class WalkTrajectory:
    """Complete walk trajectory with metadata."""
    steps: List[WalkStep] = field(default_factory=list)
    trit_sum: int = 0
    entropy: float = 0.0
    
    def add_step(self, step: WalkStep):
        self.steps.append(step)
        self.trit_sum = gf3_add(self.trit_sum, step.trit)
    
    def compute_entropy(self) -> float:
        """Compute path entropy from visit distribution."""
        if not self.steps:
            return 0.0
        
        visit_counts = defaultdict(int)
        for step in self.steps:
            visit_counts[step.box_idx] += 1
        
        n = len(self.steps)
        probs = [c / n for c in visit_counts.values()]
        self.entropy = -sum(p * np.log(p + 1e-10) for p in probs)
        return self.entropy
    
    def unique_boxes(self) -> Set[int]:
        return {step.box_idx for step in self.steps}
    
    def is_gf3_conserved(self) -> bool:
        return self.trit_sum == 0


class StringDiagramWalker:
    """
    Random walk engine for string diagrams.
    
    Supports:
    - Uniform random walk
    - Non-backtracking walk
    - Metropolis-Hastings with custom weights
    """
    
    def __init__(self, acset: StringDiagramACSet, seed: int = 0x42D):
        self.acset = acset
        self.rng = SplitMix64(seed)
        
        # Extract graph structure
        self.adjacency, self.box_to_idx = extract_box_graph(acset)
        self.n_boxes = acset.nparts("Box")
        
        # Precompute neighbors for each box
        self._neighbors: Dict[int, List[int]] = {}
        for box_idx in range(self.n_boxes):
            self._neighbors[box_idx] = [
                j for j in range(self.n_boxes) 
                if self.adjacency[box_idx, j] > 0
            ]
        
        # Compute spectral properties
        self.gap = spectral_gap(self.adjacency)
        self.mixing_time = estimate_mixing_time(self.gap, max(self.n_boxes, 1))
    
    def neighbors(self, box_idx: int) -> List[int]:
        """Get neighbors of a box in the diagram graph."""
        return self._neighbors.get(box_idx, [])
    
    def walk(self, start: int, steps: int, non_backtracking: bool = False) -> WalkTrajectory:
        """
        Execute random walk from start box.
        
        Args:
            start: Starting box index
            steps: Number of steps
            non_backtracking: If True, avoid immediately returning to previous box
        
        Returns:
            WalkTrajectory with path and GF(3) tracking
        """
        trajectory = WalkTrajectory()
        current = start
        prev = None
        
        for i in range(steps + 1):
            # Record current position
            box_name = self.acset.get_attr("Box", current, "name") or f"box_{current}"
            trit = self.acset.get_attr("Box", current, "trit") or 0
            
            step = WalkStep(
                box_idx=current,
                box_name=box_name,
                trit=trit,
                step_number=i
            )
            trajectory.add_step(step)
            
            if i >= steps:
                break
            
            # Get neighbors
            nbrs = self.neighbors(current)
            
            # Non-backtracking: exclude previous
            if non_backtracking and prev is not None:
                nbrs = [n for n in nbrs if n != prev]
            
            if not nbrs:
                break  # Dead end
            
            # Random step
            prev = current
            current = self.rng.choice(nbrs)
        
        trajectory.compute_entropy()
        return trajectory
    
    def sample_paths(self, n_paths: int, path_length: int, 
                     non_backtracking: bool = True) -> List[WalkTrajectory]:
        """Sample multiple random walk paths."""
        paths = []
        for _ in range(n_paths):
            start = self.rng.next() % max(self.n_boxes, 1)
            path = self.walk(start, path_length, non_backtracking)
            paths.append(path)
        return paths


# ═══════════════════════════════════════════════════════════════════════════════
# COMPREHENSION REGION DISCOVERY (Bumpus Model)
# ═══════════════════════════════════════════════════════════════════════════════

def discover_comprehension_regions(
    walker: StringDiagramWalker,
    n_walks: int = 100,
    threshold_quantile: float = 0.75
) -> Dict[int, List[int]]:
    """
    Discover comprehension regions via co-visitation analysis.
    
    Based on Benjamin Merlin Bumpus model: boxes frequently visited
    together form "comprehension neighborhoods" in the diagram.
    
    Returns:
        Dict mapping box_idx → list of box indices in its comprehension region
    """
    n = walker.n_boxes
    if n == 0:
        return {}
    
    # Co-visitation matrix
    co_visit = np.zeros((n, n))
    
    # Run walks
    walk_length = max(int(walker.mixing_time * 2), 10)
    
    for _ in range(n_walks):
        start = walker.rng.next() % n
        trajectory = walker.walk(start, walk_length, non_backtracking=True)
        
        # Record co-visitation within sliding window
        path = [s.box_idx for s in trajectory.steps]
        window_size = min(5, len(path))
        
        for i in range(len(path)):
            for j in range(i + 1, min(i + window_size, len(path))):
                co_visit[path[i], path[j]] += 1
                co_visit[path[j], path[i]] += 1
    
    # Threshold to find regions
    nonzero = co_visit[co_visit > 0]
    if len(nonzero) == 0:
        return {i: [i] for i in range(n)}
    
    threshold = np.quantile(nonzero, threshold_quantile)
    
    regions = {}
    for i in range(n):
        region = [j for j in range(n) if co_visit[i, j] >= threshold]
        if not region:
            region = [i]  # At least include self
        regions[i] = region
    
    return regions


# ═══════════════════════════════════════════════════════════════════════════════
# ANALYSIS AND REPORTING
# ═══════════════════════════════════════════════════════════════════════════════

def analyze_diagram_walks(
    acset: StringDiagramACSet,
    n_walks: int = 100,
    walk_length: int = 50,
    seed: int = 0x42D
) -> Dict[str, Any]:
    """
    Comprehensive analysis of random walks on a string diagram.
    
    Returns dict with:
    - Spectral properties (gap, mixing time)
    - Walk statistics (coverage, entropy, GF(3) conservation)
    - Comprehension regions
    """
    walker = StringDiagramWalker(acset, seed)
    
    # Sample walks
    trajectories = walker.sample_paths(n_walks, walk_length, non_backtracking=True)
    
    # Compute statistics
    entropies = [t.entropy for t in trajectories]
    coverages = [len(t.unique_boxes()) / max(walker.n_boxes, 1) for t in trajectories]
    conserved = sum(1 for t in trajectories if t.is_gf3_conserved())
    
    # GF(3) distribution
    trit_sums = [t.trit_sum for t in trajectories]
    trit_dist = {-1: 0, 0: 0, 1: 0}
    for ts in trit_sums:
        trit_dist[ts] = trit_dist.get(ts, 0) + 1
    
    # Comprehension regions
    regions = discover_comprehension_regions(walker, n_walks // 2)
    avg_region_size = np.mean([len(r) for r in regions.values()]) if regions else 0
    
    return {
        "diagram": {
            "n_boxes": walker.n_boxes,
            "n_wires": acset.nparts("Wire"),
            "n_types": acset.nparts("Ty"),
            "n_ports": acset.nparts("Port"),
        },
        "spectral": {
            "gap": float(walker.gap),
            "mixing_time": float(walker.mixing_time),
            "is_fast_mixing": walker.gap >= 0.25,
        },
        "walks": {
            "n_walks": n_walks,
            "walk_length": walk_length,
            "avg_entropy": float(np.mean(entropies)),
            "avg_coverage": float(np.mean(coverages)),
            "gf3_conserved_rate": conserved / max(n_walks, 1),
            "trit_distribution": trit_dist,
        },
        "comprehension": {
            "n_regions": len(regions),
            "avg_region_size": float(avg_region_size),
            "regions": {
                acset.get_attr("Box", k, "name") or f"box_{k}": [
                    acset.get_attr("Box", v, "name") or f"box_{v}" for v in vs
                ]
                for k, vs in list(regions.items())[:10]  # First 10
            }
        }
    }


def generate_report(analysis: Dict[str, Any]) -> str:
    """Generate ASCII report from analysis."""
    lines = [
        "╔════════════════════════════════════════════════════════════════════════╗",
        "║        RANDOM WALK ON STRING DIAGRAM - ANALYSIS REPORT                ║",
        "║              via ACSet Categorical Database                            ║",
        "╚════════════════════════════════════════════════════════════════════════╝",
        "",
        "DIAGRAM STRUCTURE",
        "═" * 72,
        f"  Boxes (morphisms):     {analysis['diagram']['n_boxes']}",
        f"  Wires (connections):   {analysis['diagram']['n_wires']}",
        f"  Types (objects):       {analysis['diagram']['n_types']}",
        f"  Ports (interfaces):    {analysis['diagram']['n_ports']}",
        "",
        "SPECTRAL PROPERTIES",
        "═" * 72,
        f"  Spectral Gap:          {analysis['spectral']['gap']:.4f}",
        f"  Mixing Time:           {analysis['spectral']['mixing_time']:.2f} steps",
        f"  Fast Mixing:           {'✓ YES' if analysis['spectral']['is_fast_mixing'] else '✗ NO'}",
        "",
        "RANDOM WALK STATISTICS",
        "═" * 72,
        f"  Number of walks:       {analysis['walks']['n_walks']}",
        f"  Walk length:           {analysis['walks']['walk_length']} steps",
        f"  Average entropy:       {analysis['walks']['avg_entropy']:.3f} bits",
        f"  Average coverage:      {analysis['walks']['avg_coverage'] * 100:.1f}%",
        "",
        "GF(3) CONSERVATION",
        "═" * 72,
        f"  Conservation rate:     {analysis['walks']['gf3_conserved_rate'] * 100:.1f}%",
        f"  Trit distribution:     {analysis['walks']['trit_distribution']}",
        "",
        "COMPREHENSION REGIONS (Bumpus Model)",
        "═" * 72,
        f"  Number of regions:     {analysis['comprehension']['n_regions']}",
        f"  Avg region size:       {analysis['comprehension']['avg_region_size']:.1f} boxes",
        "",
    ]
    
    if analysis['comprehension']['regions']:
        lines.append("  Sample regions:")
        for box_name, region in list(analysis['comprehension']['regions'].items())[:5]:
            lines.append(f"    {box_name}: {region[:5]}{'...' if len(region) > 5 else ''}")
    
    lines.extend([
        "",
        "═" * 72,
        "  Interpretation:",
        f"    {'High' if analysis['spectral']['gap'] >= 0.25 else 'Low'} spectral gap → "
        f"{'fast' if analysis['spectral']['gap'] >= 0.25 else 'slow'} exploration of diagram",
        f"    GF(3) conservation at {analysis['walks']['gf3_conserved_rate']*100:.0f}% → "
        f"{'balanced' if analysis['walks']['gf3_conserved_rate'] > 0.3 else 'unbalanced'} morphism composition",
        "═" * 72,
    ])
    
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# DEMO: BUILD AND WALK A TRIAD DIAGRAM
# ═══════════════════════════════════════════════════════════════════════════════

def demo():
    """Demonstrate random walks on a GF(3)-graded string diagram."""
    print("=" * 72)
    print("STRING DIAGRAM RANDOM WALK via py-ACSet")
    print("Category-theoretic exploration of morphism spaces")
    print("=" * 72)
    
    # Build a triad diagram (GF(3) balanced)
    print("\n─── Building Triad Diagram ───")
    
    diagram = (StringDiagramBuilder(seed=0x42D)
        # Types with GF(3) grading
        .add_type("Task", trit=0)
        .add_type("Validated", trit=-1)
        .add_type("Coordinated", trit=0)
        .add_type("Generated", trit=1)
        .add_type("Result", trit=0)
        
        # Triad boxes: validator (-1), coordinator (0), generator (+1)
        .add_box("validate", inputs=["Task"], outputs=["Validated"], trit=-1, layer=0)
        .add_box("coordinate", inputs=["Task"], outputs=["Coordinated"], trit=0, layer=0)
        .add_box("generate", inputs=["Task"], outputs=["Generated"], trit=1, layer=0)
        
        # Merge box (combines results)
        .add_box("merge", inputs=["Validated", "Coordinated", "Generated"], 
                 outputs=["Result"], trit=0, layer=1)
        
        # Connect triad outputs to merge inputs
        .connect("validate", 0, "merge", 0)
        .connect("coordinate", 0, "merge", 1)
        .connect("generate", 0, "merge", 2)
        
        .build())
    
    print(f"  Boxes: {diagram.nparts('Box')}")
    print(f"  Wires: {diagram.nparts('Wire')}")
    print(f"  Types: {diagram.nparts('Ty')}")
    print(f"  Ports: {diagram.nparts('Port')}")
    
    # Verify GF(3) conservation
    total_trit = sum(
        diagram.get_attr("Box", i, "trit") or 0 
        for i in range(diagram.nparts("Box"))
    )
    print(f"\n  Total GF(3) sum: {total_trit} {'✓' if total_trit == 0 else '✗'}")
    
    # Walk the diagram
    print("\n─── Random Walk Analysis ───")
    analysis = analyze_diagram_walks(diagram, n_walks=50, walk_length=20, seed=0x42D)
    
    print(generate_report(analysis))
    
    # Show a sample walk
    print("\n─── Sample Walk Trajectory ───")
    walker = StringDiagramWalker(diagram, seed=0x42D)
    sample = walker.walk(0, 10, non_backtracking=True)
    
    path_str = " → ".join(s.box_name for s in sample.steps)
    trits_str = " ".join(f"[{s.trit:+d}]" for s in sample.steps)
    
    print(f"  Path: {path_str}")
    print(f"  Trits: {trits_str}")
    print(f"  GF(3) sum: {sample.trit_sum} {'✓' if sample.is_gf3_conserved() else '✗'}")
    print(f"  Entropy: {sample.entropy:.3f} bits")
    
    # Export analysis
    print("\n─── Export ───")
    with open("/tmp/string_diagram_walk_analysis.json", "w") as f:
        json.dump(analysis, f, indent=2, default=str)
    print("  Analysis exported to /tmp/string_diagram_walk_analysis.json")
    
    return diagram, analysis


if __name__ == "__main__":
    demo()
