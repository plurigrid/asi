#!/usr/bin/env python3
"""
Edge Phase Propagator (Scoped) - Phase-aware Overlap Manager
MINUS (-1) agent enhancement | Seed: 0x42D | Trit: -1

Extends the base EdgePhasePropagator with phase-scoped overlaps:
- Tracks adhesion edges within phase boundaries
- Enforces sheaf conditions per phase
- Propagates phase constraints across edges
- Uses GF(3) conservation for phase coloring

Based on StructuredDecompositions.jl adhesion_filter algorithm
with phase-aware scoping from DecidingSheaves.jl
"""

from dataclasses import dataclass, field
from typing import Any, Callable, Generic, TypeVar, Optional, Dict, List, Tuple, Set
from enum import IntEnum
import hashlib
from collections import defaultdict

T = TypeVar('T')

class Trit(IntEnum):
    """GF(3) trit values for overlap phase states."""
    MINUS = -1   # Constraint/verification
    ZERO = 0     # Neutral/identity
    PLUS = 1     # Generation/expansion

    def __add__(self, other: 'Trit') -> 'Trit':
        """GF(3) addition."""
        result = (self.value + other.value) % 3
        return Trit(result - 1 if result != 0 else 0)

    def __neg__(self) -> 'Trit':
        """GF(3) negation."""
        return Trit(-self.value if self.value != 0 else 0)

    def __mul__(self, other: 'Trit') -> 'Trit':
        """GF(3) multiplication."""
        result = (self.value * other.value) % 3
        return Trit(result - 1 if result != 0 else 0)

class Phase(IntEnum):
    """Phase enumeration for scoped propagation."""
    PHASE_1 = 1  # Acquisition/Collection
    PHASE_2 = 2  # Validation/Filtering
    PHASE_3 = 3  # Integration/Synthesis
    PHASE_4 = 4  # Production/Deployment
    ALL = 0      # Cross-phase

@dataclass
class Bag(Generic[T]):
    """A bag in a tree decomposition."""
    id: str
    elements: Set[T]
    phase: Phase = Phase.PHASE_1
    local_data: Dict[str, Any] = field(default_factory=dict)
    trit_phase: Trit = Trit.ZERO
    phase_constraints: Dict[Phase, Set[str]] = field(default_factory=dict)

    def __hash__(self):
        return hash(self.id)

    def add_phase_constraint(self, phase: Phase, constraint: str) -> None:
        """Add constraint for specific phase."""
        if phase not in self.phase_constraints:
            self.phase_constraints[phase] = set()
        self.phase_constraints[phase].add(constraint)

    def get_phase_constraints(self, phase: Phase) -> Set[str]:
        """Get constraints applicable to phase."""
        constraints = set()
        if phase in self.phase_constraints:
            constraints.update(self.phase_constraints[phase])
        if Phase.ALL in self.phase_constraints:
            constraints.update(self.phase_constraints[Phase.ALL])
        return constraints

@dataclass
class Adhesion(Generic[T]):
    """
    An adhesion edge between two bags, scoped to phases.
    Represents the overlap/intersection that must satisfy sheaf condition
    per phase.
    """
    left_bag: Bag[T]
    right_bag: Bag[T]
    overlap: Set[T]
    phases: Set[Phase] = field(default_factory=lambda: {Phase.PHASE_1})

    # Per-phase restrictions
    left_restrictions: Dict[Phase, Dict[str, Any]] = field(default_factory=dict)
    right_restrictions: Dict[Phase, Dict[str, Any]] = field(default_factory=dict)
    trit_colors: Dict[Phase, Trit] = field(default_factory=dict)

    def __post_init__(self):
        """Initialize per-phase data structures."""
        for phase in self.phases:
            if phase not in self.left_restrictions:
                self.left_restrictions[phase] = {}
            if phase not in self.right_restrictions:
                self.right_restrictions[phase] = {}
            if phase not in self.trit_colors:
                # Deterministic color per phase
                self.trit_colors[phase] = Trit.ZERO

    @property
    def id(self) -> str:
        return f"{self.left_bag.id}--{self.right_bag.id}"

    def phase_id(self, phase: Phase) -> str:
        """Get phase-scoped identifier."""
        return f"{self.id}@PHASE_{phase.value}"

    def satisfies_sheaf_condition(self, phase: Phase) -> bool:
        """
        Check if local data agrees on the overlap for specific phase.
        Sheaf condition: restrictions from both sides must match.
        """
        if phase not in self.left_restrictions:
            return True

        left_restr = self.left_restrictions[phase]
        right_restr = self.right_restrictions[phase]

        for key in left_restr:
            if key in right_restr:
                if left_restr[key] != right_restr[key]:
                    return False
        return True

@dataclass
class EdgePhaseState:
    """State of an edge in a specific phase."""
    adhesion: Adhesion
    phase: Phase
    trit_phase: Trit
    is_filtered: bool = False
    pullback_elements: Optional[Set] = None
    satisfied: bool = True

class EdgePhasePropagatorScoped:
    """
    Phase-scoped adhesion edge manager for structured decompositions.

    Extends base propagator with:
    - Per-phase edge tracking
    - Phase-scoped sheaf conditions
    - Cross-phase constraint propagation
    - GF(3) conservation per phase
    """

    def __init__(self, seed: int = 0x42D, phases: Optional[List[Phase]] = None):
        self.bags: Dict[str, Bag] = {}
        self.adhesions: List[Adhesion] = []
        self.edge_states: Dict[str, EdgePhaseState] = {}
        self.phase_edge_states: Dict[Phase, Dict[str, EdgePhaseState]] = defaultdict(dict)
        self.seed = seed
        self.phases = phases or [Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3, Phase.PHASE_4]
        self._trit_sums: Dict[Phase, Trit] = {phase: Trit.ZERO for phase in self.phases}
        self._phase_order = {phase: i for i, phase in enumerate(self.phases)}

    def add_bag(self, bag: Bag) -> None:
        """Add a bag to the decomposition."""
        self.bags[bag.id] = bag

    def add_adhesion(self, left_id: str, right_id: str, phases: Optional[Set[Phase]] = None) -> Adhesion:
        """
        Create a phase-scoped adhesion edge between two bags.
        """
        left = self.bags[left_id]
        right = self.bags[right_id]

        # Default to both bags' phases if not specified
        if phases is None:
            phases = {left.phase, right.phase}

        # Compute overlap (intersection)
        overlap = left.elements & right.elements

        adhesion = Adhesion(
            left_bag=left,
            right_bag=right,
            overlap=overlap,
            phases=phases
        )

        # Assign trit colors per phase
        for phase in phases:
            color_hash = int(hashlib.sha256(
                f"{self.seed}:{left_id}:{right_id}:{phase.value}".encode()
            ).hexdigest()[:8], 16)
            adhesion.trit_colors[phase] = Trit((color_hash % 3) - 1)
            self._trit_sums[phase] = self._trit_sums[phase] + adhesion.trit_colors[phase]

            # Create phase-scoped edge state
            state = EdgePhaseState(
                adhesion=adhesion,
                phase=phase,
                trit_phase=adhesion.trit_colors[phase]
            )
            self.phase_edge_states[phase][adhesion.phase_id(phase)] = state

        self.adhesions.append(adhesion)
        return adhesion

    def set_local_data(self, bag_id: str, key: str, value: Any, phase: Optional[Phase] = None) -> None:
        """Set local data on a bag for specific phase."""
        bag = self.bags[bag_id]
        bag.local_data[key] = value

        # Propagate to adhesions in relevant phases
        target_phases = {phase} if phase else self.phases
        self._propagate_to_adhesions(bag_id, key, value, target_phases)

    def _propagate_to_adhesions(self, bag_id: str, key: str, value: Any, phases: Set[Phase]) -> None:
        """Propagate local data to adjacent adhesion edges in phases."""
        for adhesion in self.adhesions:
            for phase in phases:
                if phase not in adhesion.phases:
                    continue

                if adhesion.left_bag.id == bag_id:
                    adhesion.left_restrictions[phase][key] = value
                elif adhesion.right_bag.id == bag_id:
                    adhesion.right_restrictions[phase][key] = value

    def adhesion_filter(self, adhesion_idx: int, phase: Phase) -> bool:
        """
        Apply adhesion filter to an edge in specific phase.

        Returns True if filter preserves non-empty overlap.
        """
        if adhesion_idx >= len(self.adhesions):
            raise IndexError(f"Adhesion index {adhesion_idx} out of range")

        adhesion = self.adhesions[adhesion_idx]
        if phase not in adhesion.phases:
            return True  # Not applicable to this phase

        state_key = adhesion.phase_id(phase)
        if state_key not in self.phase_edge_states[phase]:
            return False

        state = self.phase_edge_states[phase][state_key]

        # Compute pullback: elements that satisfy both restrictions in this phase
        pullback = set()
        left_restr = adhesion.left_restrictions[phase]
        right_restr = adhesion.right_restrictions[phase]

        for elem in adhesion.overlap:
            left_ok = all(
                adhesion.left_bag.local_data.get(k) == v
                for k, v in left_restr.items()
                if k in adhesion.left_bag.local_data
            )
            right_ok = all(
                adhesion.right_bag.local_data.get(k) == v
                for k, v in right_restr.items()
                if k in adhesion.right_bag.local_data
            )
            if left_ok and right_ok:
                pullback.add(elem)

        state.pullback_elements = pullback
        state.is_filtered = True
        return len(pullback) > 0

    def decide_sheaf(self, phase: Optional[Phase] = None) -> Tuple[bool, List[EdgePhaseState]]:
        """
        Solve decision problem via sheaf condition.

        If phase is None, check all phases.
        Returns: (satisfiable, witness_states)
        """
        phases_to_check = {phase} if phase else set(self.phases)
        witness = []

        for check_phase in phases_to_check:
            for i, adhesion in enumerate(self.adhesions):
                if check_phase not in adhesion.phases:
                    continue

                if not self.adhesion_filter(i, check_phase):
                    return (False, witness)

                state = self.phase_edge_states[check_phase][adhesion.phase_id(check_phase)]
                witness.append(state)

                if not adhesion.satisfies_sheaf_condition(check_phase):
                    return (False, witness)

        return (True, witness)

    def verify_gf3_conservation(self, phase: Optional[Phase] = None) -> bool:
        """Verify GF(3) sum is conserved."""
        if phase:
            return self._trit_sums[phase] == Trit.ZERO
        return all(s == Trit.ZERO for s in self._trit_sums.values())

    def get_phase_order(self) -> Dict[Phase, int]:
        """Get phase ordering for dependency resolution."""
        return self._phase_order

    def propagate_phase_forward(self, source_phase: Phase, target_phase: Phase) -> None:
        """Propagate constraints from one phase to the next."""
        if target_phase not in self.phases:
            return

        source_order = self._phase_order.get(source_phase, -1)
        target_order = self._phase_order.get(target_phase, -1)

        if source_order >= target_order:
            return  # Can only propagate forward

        # Copy forward-applicable data
        for adhesion in self.adhesions:
            if source_phase in adhesion.phases and target_phase in adhesion.phases:
                # Merge restrictions from source to target
                if source_phase in adhesion.left_restrictions:
                    adhesion.left_restrictions[target_phase].update(
                        adhesion.left_restrictions[source_phase]
                    )
                if source_phase in adhesion.right_restrictions:
                    adhesion.right_restrictions[target_phase].update(
                        adhesion.right_restrictions[source_phase]
                    )

    def get_overlay_coloring(self, phase: Optional[Phase] = None) -> Dict[str, Trit]:
        """Get GF(3) coloring of overlaps."""
        if phase:
            return {
                adhesion.phase_id(phase): adhesion.trit_colors.get(phase, Trit.ZERO)
                for adhesion in self.adhesions
                if phase in adhesion.phases
            }
        return {
            f"{a.id}@ALL": a.trit_colors.get(Phase.ALL, Trit.ZERO)
            for a in self.adhesions
        }

    def summary(self, phase: Optional[Phase] = None) -> Dict:
        """Return summary of propagator state."""
        phases = {phase} if phase else set(self.phases)

        summaries = {}
        for p in phases:
            edge_states = self.phase_edge_states[p]
            summaries[f"Phase_{p.value}"] = {
                "bags": len(self.bags),
                "adhesions": len([a for a in self.adhesions if p in a.phases]),
                "gf3_sum": self._trit_sums[p].value,
                "gf3_conserved": self._trit_sums[p] == Trit.ZERO,
                "all_filtered": all(s.is_filtered for s in edge_states.values()),
                "sheaf_satisfiable": all(
                    a.satisfies_sheaf_condition(p)
                    for a in self.adhesions
                    if p in a.phases
                ),
                "edge_states": len(edge_states)
            }

        return {
            "phases": summaries,
            "total_bags": len(self.bags),
            "total_adhesions": len(self.adhesions),
            "all_gf3_conserved": self.verify_gf3_conservation()
        }


def demo():
    """Demonstrate phase-scoped edge propagator."""
    print("Edge Phase Propagator (Scoped) Demo")
    print("=" * 50)

    # Create propagator
    phases = [Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3]
    prop = EdgePhasePropagatorScoped(seed=0x42D, phases=phases)

    # Create bags with phases
    prop.add_bag(Bag(id="B1", elements={1, 2, 3}, phase=Phase.PHASE_1))
    prop.add_bag(Bag(id="B2", elements={2, 3, 4}, phase=Phase.PHASE_2))
    prop.add_bag(Bag(id="B3", elements={3, 4, 5}, phase=Phase.PHASE_3))

    # Create adhesions spanning phases
    a1 = prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1, Phase.PHASE_2})
    a2 = prop.add_adhesion("B2", "B3", phases={Phase.PHASE_2, Phase.PHASE_3})

    print(f"\nBags: {list(prop.bags.keys())}")
    print(f"\nAdhesion B1--B2:")
    for phase in [Phase.PHASE_1, Phase.PHASE_2]:
        print(f"  Phase {phase.value}: overlap={a1.overlap}, trit={a1.trit_colors[phase].name}")

    print(f"\nAdhesion B2--B3:")
    for phase in [Phase.PHASE_2, Phase.PHASE_3]:
        print(f"  Phase {phase.value}: overlap={a2.overlap}, trit={a2.trit_colors[phase].name}")

    # Set phase-specific data
    prop.set_local_data("B1", "status", "acquired", Phase.PHASE_1)
    prop.set_local_data("B2", "status", "acquired", Phase.PHASE_1)
    prop.set_local_data("B2", "status", "validated", Phase.PHASE_2)
    prop.set_local_data("B3", "status", "validated", Phase.PHASE_2)

    # Check per-phase sheaf conditions
    print(f"\nSheaf conditions:")
    for check_phase in phases:
        satisfiable, witness = prop.decide_sheaf(check_phase)
        print(f"  Phase {check_phase.value}: satisfiable={satisfiable}")

    # Verify GF(3) conservation
    print(f"\nGF(3) Conservation:")
    for check_phase in phases:
        conserved = prop.verify_gf3_conservation(check_phase)
        print(f"  Phase {check_phase.value}: conserved={conserved}")

    print(f"\nComplete Summary:\n{prop.summary()}")


if __name__ == "__main__":
    demo()
