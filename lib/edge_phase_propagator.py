#!/usr/bin/env python3
"""
Edge Phase Propagator - Overlap Manager for Structured Decompositions
MINUS (-1) agent contribution | Seed: 0x42D | Trit: -1

Based on StructuredDecompositions.jl adhesion patterns:
- Tracks adhesion edges between bags
- Ensures sheaf condition (local data agrees on overlaps)
- Uses GF(3) conservation for coloring overlaps

Reference: DecidingSheaves.jl adhesion_filter algorithm
"""

from dataclasses import dataclass, field
from typing import Any, Callable, Generic, TypeVar, Optional
from enum import IntEnum
import hashlib

T = TypeVar('T')

class Trit(IntEnum):
    """GF(3) trit values for overlap phase states."""
    MINUS = -1   # Constraint/verification
    ZERO = 0     # Neutral/identity
    PLUS = 1     # Generation/expansion
    
    def __add__(self, other: 'Trit') -> 'Trit':
        """GF(3) addition."""
        return Trit((self.value + other.value) % 3 - 1 if (self.value + other.value) % 3 != 0 else 0)
    
    def __neg__(self) -> 'Trit':
        """GF(3) negation."""
        return Trit(-self.value)
    
    def __mul__(self, other: 'Trit') -> 'Trit':
        """GF(3) multiplication."""
        return Trit(self.value * other.value)

@dataclass
class Bag(Generic[T]):
    """A bag in a tree decomposition."""
    id: str
    elements: set[T]
    local_data: dict[str, Any] = field(default_factory=dict)
    trit_phase: Trit = Trit.ZERO
    
    def __hash__(self):
        return hash(self.id)

@dataclass  
class Adhesion(Generic[T]):
    """
    An adhesion edge between two bags.
    Represents the overlap/intersection that must satisfy sheaf condition.
    """
    left_bag: Bag[T]
    right_bag: Bag[T]
    overlap: set[T]  # Elements in common
    left_restriction: dict[str, Any] = field(default_factory=dict)
    right_restriction: dict[str, Any] = field(default_factory=dict)
    trit_color: Trit = Trit.ZERO
    
    @property
    def id(self) -> str:
        return f"{self.left_bag.id}--{self.right_bag.id}"
    
    def satisfies_sheaf_condition(self) -> bool:
        """
        Check if local data agrees on the overlap.
        Sheaf condition: restrictions from both sides must match.
        """
        for key in self.left_restriction:
            if key in self.right_restriction:
                if self.left_restriction[key] != self.right_restriction[key]:
                    return False
        return True

@dataclass
class EdgePhaseState:
    """State of an edge in the propagation."""
    adhesion: Adhesion
    phase: Trit
    is_filtered: bool = False
    pullback_elements: Optional[set] = None

class EdgePhasePropagator:
    """
    Manages overlaps between bags in a structured decomposition.
    
    Implements the adhesion_filter algorithm from DecidingSheaves.jl:
    1. For each adhesion edge, compute pullback of restrictions
    2. Project back to bags (filtering)
    3. Check for empty bags (decision problem)
    
    Uses GF(3) conservation to color overlaps:
    - Sum of trit phases around any cycle = 0 (mod 3)
    """
    
    def __init__(self, seed: int = 0x42D):
        self.bags: dict[str, Bag] = {}
        self.adhesions: list[Adhesion] = []
        self.edge_states: dict[str, EdgePhaseState] = {}
        self.seed = seed
        self._trit_sum = Trit.ZERO
    
    def add_bag(self, bag: Bag) -> None:
        """Add a bag to the decomposition."""
        self.bags[bag.id] = bag
    
    def add_adhesion(self, left_id: str, right_id: str) -> Adhesion:
        """
        Create an adhesion edge between two bags.
        Automatically computes overlap and assigns GF(3) color.
        """
        left = self.bags[left_id]
        right = self.bags[right_id]
        
        # Compute overlap (intersection)
        overlap = left.elements & right.elements
        
        # Assign trit color based on deterministic hash
        color_hash = int(hashlib.sha256(
            f"{self.seed}:{left_id}:{right_id}".encode()
        ).hexdigest()[:8], 16)
        trit_color = Trit((color_hash % 3) - 1)
        
        adhesion = Adhesion(
            left_bag=left,
            right_bag=right,
            overlap=overlap,
            trit_color=trit_color
        )
        self.adhesions.append(adhesion)
        
        # Initialize edge state
        self.edge_states[adhesion.id] = EdgePhaseState(
            adhesion=adhesion,
            phase=trit_color
        )
        
        # Update GF(3) sum
        self._trit_sum = self._trit_sum + trit_color
        
        return adhesion
    
    def set_local_data(self, bag_id: str, key: str, value: Any) -> None:
        """Set local data on a bag."""
        self.bags[bag_id].local_data[key] = value
        self._propagate_to_adhesions(bag_id, key, value)
    
    def _propagate_to_adhesions(self, bag_id: str, key: str, value: Any) -> None:
        """Propagate local data to adjacent adhesion edges."""
        for adhesion in self.adhesions:
            if adhesion.left_bag.id == bag_id:
                adhesion.left_restriction[key] = value
            elif adhesion.right_bag.id == bag_id:
                adhesion.right_restriction[key] = value
    
    def adhesion_filter(self, adhesion_idx: int) -> bool:
        """
        Apply adhesion filter to an edge (Algorithm from DecidingSheaves.jl).
        
        Computes the pullback of restrictions and projects back.
        Returns True if filter preserves non-empty bags.
        """
        if adhesion_idx >= len(self.adhesions):
            raise IndexError(f"Adhesion index {adhesion_idx} out of range")
        
        adhesion = self.adhesions[adhesion_idx]
        state = self.edge_states[adhesion.id]
        
        # Compute pullback: elements that satisfy both restrictions
        pullback = set()
        for elem in adhesion.overlap:
            # Check if element is consistent with both sides
            left_ok = all(
                adhesion.left_bag.local_data.get(k) == v
                for k, v in adhesion.left_restriction.items()
                if k in adhesion.left_bag.local_data
            )
            right_ok = all(
                adhesion.right_bag.local_data.get(k) == v
                for k, v in adhesion.right_restriction.items()
                if k in adhesion.right_bag.local_data
            )
            if left_ok and right_ok:
                pullback.add(elem)
        
        state.pullback_elements = pullback
        state.is_filtered = True
        
        # Project back: update bag elements based on pullback
        # (In full implementation, would update bags)
        
        return len(pullback) > 0
    
    def decide_sheaf(self) -> tuple[bool, list[EdgePhaseState]]:
        """
        Solve decision problem via sheaf condition.
        
        Returns:
            (satisfiable, witness_states)
        """
        witness = []
        
        for i, adhesion in enumerate(self.adhesions):
            if not self.adhesion_filter(i):
                # Empty pullback means constraint unsatisfiable
                return (False, witness)
            
            state = self.edge_states[adhesion.id]
            witness.append(state)
            
            # Check sheaf condition
            if not adhesion.satisfies_sheaf_condition():
                return (False, witness)
        
        return (True, witness)
    
    def verify_gf3_conservation(self) -> bool:
        """Verify GF(3) sum is conserved (should be 0 for closed loops)."""
        return self._trit_sum == Trit.ZERO
    
    def get_overlap_coloring(self) -> dict[str, Trit]:
        """Get GF(3) coloring of all overlaps."""
        return {
            adhesion.id: adhesion.trit_color
            for adhesion in self.adhesions
        }
    
    def summary(self) -> dict:
        """Return summary of propagator state."""
        return {
            "bags": len(self.bags),
            "adhesions": len(self.adhesions),
            "gf3_sum": self._trit_sum.value,
            "gf3_conserved": self.verify_gf3_conservation(),
            "all_filtered": all(s.is_filtered for s in self.edge_states.values()),
            "sheaf_satisfiable": all(
                a.satisfies_sheaf_condition() for a in self.adhesions
            )
        }


def demo():
    """Demonstrate edge phase propagator with 3-coloring example."""
    print("Edge Phase Propagator Demo")
    print("=" * 40)
    
    # Create propagator with seed
    prop = EdgePhasePropagator(seed=0x42D)
    
    # Create bags (nodes in tree decomposition)
    prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
    prop.add_bag(Bag(id="B2", elements={2, 3, 4}))
    prop.add_bag(Bag(id="B3", elements={3, 4, 5}))
    
    # Create adhesion edges
    a1 = prop.add_adhesion("B1", "B2")
    a2 = prop.add_adhesion("B2", "B3")
    
    print(f"\nBags: {list(prop.bags.keys())}")
    print(f"Adhesion B1--B2 overlap: {a1.overlap}, trit: {a1.trit_color.name}")
    print(f"Adhesion B2--B3 overlap: {a2.overlap}, trit: {a2.trit_color.name}")
    
    # Set some local data (e.g., partial coloring)
    prop.set_local_data("B1", "color_2", "red")
    prop.set_local_data("B2", "color_2", "red")  # Agrees on overlap
    prop.set_local_data("B2", "color_3", "blue")
    prop.set_local_data("B3", "color_3", "blue")  # Agrees on overlap
    
    # Check sheaf condition
    satisfiable, witness = prop.decide_sheaf()
    
    print(f"\nSheaf satisfiable: {satisfiable}")
    print(f"GF(3) conserved: {prop.verify_gf3_conservation()}")
    print(f"\nSummary: {prop.summary()}")


if __name__ == "__main__":
    demo()
