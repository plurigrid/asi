#!/usr/bin/env python3
"""
Test suite for Edge Phase Propagator (Scoped)

Tests phase-aware adhesion edge management:
- Per-phase edge tracking
- Phase-scoped sheaf conditions
- Cross-phase constraint propagation
- GF(3) conservation per phase
"""

import pytest
import sys
sys.path.insert(0, '../lib')

from edge_phase_propagator_scoped import (
    EdgePhasePropagatorScoped, Bag, Adhesion, EdgePhaseState,
    Phase, Trit
)


class TestPhaseScoping:
    """Test phase scoping in edge propagator."""

    def test_phase_enumeration(self):
        """Test Phase enum values."""
        assert Phase.PHASE_1.value == 1
        assert Phase.PHASE_2.value == 2
        assert Phase.PHASE_3.value == 3
        assert Phase.PHASE_4.value == 4
        assert Phase.ALL.value == 0

    def test_bag_phase_constraints(self):
        """Test adding and retrieving phase constraints."""
        bag = Bag(id="B1", elements={1, 2, 3}, phase=Phase.PHASE_1)

        bag.add_phase_constraint(Phase.PHASE_1, "acquired")
        bag.add_phase_constraint(Phase.PHASE_2, "validated")
        bag.add_phase_constraint(Phase.ALL, "exists")

        assert "acquired" in bag.get_phase_constraints(Phase.PHASE_1)
        assert "exists" in bag.get_phase_constraints(Phase.PHASE_1)
        assert "validated" in bag.get_phase_constraints(Phase.PHASE_2)
        assert "exists" in bag.get_phase_constraints(Phase.PHASE_2)

    def test_trit_arithmetic(self):
        """Test GF(3) arithmetic."""
        assert Trit.MINUS + Trit.ZERO == Trit.MINUS
        assert Trit.MINUS + Trit.PLUS == Trit.ZERO
        assert Trit.PLUS + Trit.PLUS == Trit.MINUS
        assert -Trit.PLUS == Trit.MINUS
        assert Trit.PLUS * Trit.MINUS == Trit.MINUS

    def test_propagator_creation(self):
        """Test creating scoped propagator."""
        phases = [Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3]
        prop = EdgePhasePropagatorScoped(seed=0x42D, phases=phases)

        assert len(prop.phases) == 3
        assert prop.seed == 0x42D
        assert all(phase in prop._trit_sums for phase in phases)

    def test_add_bags_with_phases(self):
        """Test adding bags with different phases."""
        prop = EdgePhasePropagatorScoped()

        prop.add_bag(Bag(id="B1", elements={1, 2}, phase=Phase.PHASE_1))
        prop.add_bag(Bag(id="B2", elements={2, 3}, phase=Phase.PHASE_2))
        prop.add_bag(Bag(id="B3", elements={3, 4}, phase=Phase.PHASE_3))

        assert len(prop.bags) == 3
        assert prop.bags["B1"].phase == Phase.PHASE_1
        assert prop.bags["B2"].phase == Phase.PHASE_2
        assert prop.bags["B3"].phase == Phase.PHASE_3

    def test_add_adhesion_single_phase(self):
        """Test adding adhesion to single phase."""
        prop = EdgePhasePropagatorScoped()
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))

        adhesion = prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1})

        assert adhesion.overlap == {2, 3}
        assert Phase.PHASE_1 in adhesion.phases
        assert Phase.PHASE_1 in adhesion.trit_colors

    def test_add_adhesion_multi_phase(self):
        """Test adding adhesion spanning multiple phases."""
        prop = EdgePhasePropagatorScoped()
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))

        adhesion = prop.add_adhesion(
            "B1", "B2",
            phases={Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3}
        )

        assert adhesion.overlap == {2, 3}
        assert len(adhesion.phases) == 3
        assert all(phase in adhesion.trit_colors for phase in [Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3])

    def test_adhesion_phase_id(self):
        """Test phase-scoped adhesion IDs."""
        prop = EdgePhasePropagatorScoped()
        prop.add_bag(Bag(id="B1", elements={1, 2}))
        prop.add_bag(Bag(id="B2", elements={2, 3}))

        adhesion = prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1, Phase.PHASE_2})

        assert adhesion.phase_id(Phase.PHASE_1) == "B1--B2@PHASE_1"
        assert adhesion.phase_id(Phase.PHASE_2) == "B1--B2@PHASE_2"

    def test_set_local_data_phase_specific(self):
        """Test setting phase-specific local data."""
        prop = EdgePhasePropagatorScoped()
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))
        prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1, Phase.PHASE_2})

        prop.set_local_data("B1", "status", "phase1_done", Phase.PHASE_1)
        prop.set_local_data("B2", "status", "phase2_done", Phase.PHASE_2)

        assert prop.bags["B1"].local_data["status"] == "phase1_done"
        assert prop.bags["B2"].local_data["status"] == "phase2_done"

    def test_sheaf_condition_phase_specific(self):
        """Test sheaf condition checking per phase."""
        prop = EdgePhasePropagatorScoped()
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))
        adhesion = prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1, Phase.PHASE_2})

        # Set matching data on Phase.PHASE_1
        prop.set_local_data("B1", "color", "red", Phase.PHASE_1)
        prop.set_local_data("B2", "color", "red", Phase.PHASE_1)

        # Set conflicting data on Phase.PHASE_2
        prop.set_local_data("B1", "color", "blue", Phase.PHASE_2)
        prop.set_local_data("B2", "color", "red", Phase.PHASE_2)

        assert adhesion.satisfies_sheaf_condition(Phase.PHASE_1) == True
        assert adhesion.satisfies_sheaf_condition(Phase.PHASE_2) == False

    def test_gf3_conservation_per_phase(self):
        """Test GF(3) conservation tracking per phase."""
        prop = EdgePhasePropagatorScoped()
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))
        prop.add_bag(Bag(id="B3", elements={3, 4, 5}))

        # Create cycle of adhesions
        prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1})
        prop.add_adhesion("B2", "B3", phases={Phase.PHASE_1})
        prop.add_adhesion("B3", "B1", phases={Phase.PHASE_1})

        # Cycle should conserve GF(3)
        assert prop.verify_gf3_conservation(Phase.PHASE_1) == True

    def test_adhesion_filter_single_phase(self):
        """Test adhesion filtering in single phase."""
        prop = EdgePhasePropagatorScoped()
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))
        prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1})

        # Set matching data to ensure pullback is non-empty
        prop.set_local_data("B1", "color_2", "red", Phase.PHASE_1)
        prop.set_local_data("B2", "color_2", "red", Phase.PHASE_1)

        result = prop.adhesion_filter(0, Phase.PHASE_1)
        assert result == True

    def test_decide_sheaf_single_phase(self):
        """Test sheaf decision in single phase."""
        prop = EdgePhasePropagatorScoped()
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))
        prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1})

        # Set matching data
        prop.set_local_data("B1", "status", "ok", Phase.PHASE_1)
        prop.set_local_data("B2", "status", "ok", Phase.PHASE_1)

        satisfiable, witness = prop.decide_sheaf(Phase.PHASE_1)
        assert satisfiable == True
        assert len(witness) > 0

    def test_decide_sheaf_all_phases(self):
        """Test sheaf decision across all phases."""
        prop = EdgePhasePropagatorScoped(phases=[Phase.PHASE_1, Phase.PHASE_2])
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))
        prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1, Phase.PHASE_2})

        # Set consistent data for both phases
        for phase in [Phase.PHASE_1, Phase.PHASE_2]:
            prop.set_local_data("B1", "status", "ok", phase)
            prop.set_local_data("B2", "status", "ok", phase)

        satisfiable, witness = prop.decide_sheaf(None)
        assert satisfiable == True

    def test_phase_forward_propagation(self):
        """Test constraint propagation from one phase to next."""
        prop = EdgePhasePropagatorScoped(
            phases=[Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3]
        )
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))
        adhesion = prop.add_adhesion(
            "B1", "B2",
            phases={Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3}
        )

        # Set data in Phase.PHASE_1
        prop.set_local_data("B1", "acquired", True, Phase.PHASE_1)

        # Propagate forward
        prop.propagate_phase_forward(Phase.PHASE_1, Phase.PHASE_2)

        # Data should be available in Phase.PHASE_2
        assert "acquired" in adhesion.left_restrictions[Phase.PHASE_2]

    def test_phase_order(self):
        """Test phase ordering."""
        phases = [Phase.PHASE_1, Phase.PHASE_3, Phase.PHASE_2]
        prop = EdgePhasePropagatorScoped(phases=phases)

        order = prop.get_phase_order()
        assert order[Phase.PHASE_1] == 0
        assert order[Phase.PHASE_3] == 1
        assert order[Phase.PHASE_2] == 2

    def test_get_overlay_coloring_per_phase(self):
        """Test getting phase-specific overlap coloring."""
        prop = EdgePhasePropagatorScoped()
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))
        prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1, Phase.PHASE_2})

        coloring_p1 = prop.get_overlay_coloring(Phase.PHASE_1)
        coloring_p2 = prop.get_overlay_coloring(Phase.PHASE_2)

        assert "B1--B2@PHASE_1" in coloring_p1
        assert "B1--B2@PHASE_2" in coloring_p2
        assert isinstance(coloring_p1["B1--B2@PHASE_1"], Trit)

    def test_summary_per_phase(self):
        """Test summary generation per phase."""
        prop = EdgePhasePropagatorScoped(phases=[Phase.PHASE_1, Phase.PHASE_2])
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}))
        prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1, Phase.PHASE_2})

        summary_p1 = prop.summary(Phase.PHASE_1)
        assert "Phase_1" in summary_p1["phases"]
        assert summary_p1["phases"]["Phase_1"]["bags"] == 2
        assert summary_p1["phases"]["Phase_1"]["adhesions"] == 1

    def test_full_workflow(self):
        """Test complete phase-aware workflow."""
        prop = EdgePhasePropagatorScoped(
            phases=[Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3]
        )

        # Phase 1: Data acquisition
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}, phase=Phase.PHASE_1))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}, phase=Phase.PHASE_1))

        # Phase 2: Validation
        prop.add_bag(Bag(id="B3", elements={3, 4, 5}, phase=Phase.PHASE_2))

        # Create phase-spanning adhesions
        a1 = prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1})
        a2 = prop.add_adhesion("B2", "B3", phases={Phase.PHASE_1, Phase.PHASE_2})

        # Set phase-specific data
        prop.set_local_data("B1", "source", "sensor1", Phase.PHASE_1)
        prop.set_local_data("B2", "source", "sensor1", Phase.PHASE_1)
        prop.set_local_data("B2", "validated", True, Phase.PHASE_2)
        prop.set_local_data("B3", "validated", True, Phase.PHASE_2)

        # Check Phase 1
        satisfiable_p1, _ = prop.decide_sheaf(Phase.PHASE_1)
        assert satisfiable_p1 == True

        # Propagate constraints forward
        prop.propagate_phase_forward(Phase.PHASE_1, Phase.PHASE_2)

        # Check Phase 2
        satisfiable_p2, _ = prop.decide_sheaf(Phase.PHASE_2)
        assert satisfiable_p2 == True

        # Get overall summary
        summary = prop.summary()
        assert summary["total_bags"] == 3
        assert summary["total_adhesions"] == 2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
