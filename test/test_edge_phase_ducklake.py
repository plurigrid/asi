#!/usr/bin/env python3
"""
Test suite for Edge Phase Propagator DuckLake Integration

Tests persistence, loading, and querying of phase-scoped edge states
in DuckLake database backend.
"""

import pytest
import sys
import tempfile
import json
from pathlib import Path

sys.path.insert(0, '../lib')

from edge_phase_propagator_scoped import (
    EdgePhasePropagatorScoped, Bag, Adhesion, Phase, Trit
)
from edge_phase_ducklake import EdgePhaseDuckLake


class TestEdgePhaseDuckLake:
    """Test DuckLake persistence layer."""

    @pytest.fixture
    def temp_db(self):
        """Create temporary database."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name
        yield db_path
        Path(db_path).unlink(missing_ok=True)

    @pytest.fixture
    def sample_propagator(self):
        """Create sample propagator with test data."""
        prop = EdgePhasePropagatorScoped(
            phases=[Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3]
        )

        # Add bags
        prop.add_bag(Bag(id="B1", elements={1, 2, 3}, phase=Phase.PHASE_1))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}, phase=Phase.PHASE_1))
        prop.add_bag(Bag(id="B3", elements={3, 4, 5}, phase=Phase.PHASE_2))

        # Add adhesions
        prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1})
        prop.add_adhesion("B2", "B3", phases={Phase.PHASE_1, Phase.PHASE_2})

        # Set data
        prop.set_local_data("B1", "status", "acquired", Phase.PHASE_1)
        prop.set_local_data("B2", "status", "acquired", Phase.PHASE_1)
        prop.set_local_data("B3", "status", "validated", Phase.PHASE_2)

        return prop

    def test_schema_creation(self, temp_db):
        """Test that schema is created correctly."""
        with EdgePhaseDuckLake(temp_db) as db:
            # Check that all tables exist
            tables = db.conn.execute(
                "SELECT name FROM duckdb_tables() WHERE schema_name='main'"
            ).fetchall()

            table_names = {t[0] for t in tables}
            expected_tables = {
                'bags', 'adhesions', 'phase_edges', 'phase_states',
                'bag_local_data', 'phase_dependencies'
            }

            assert expected_tables.issubset(table_names)

    def test_persist_simple_propagator(self, temp_db, sample_propagator):
        """Test persisting a simple propagator."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

            # Verify bags were stored
            bags = db.conn.execute(
                "SELECT COUNT(*) FROM bags WHERE world_id = ?",
                ["test_world"]
            ).fetchone()
            assert bags[0] == 3

            # Verify adhesions were stored
            adhesions = db.conn.execute(
                "SELECT COUNT(*) FROM adhesions WHERE world_id = ?",
                ["test_world"]
            ).fetchone()
            assert adhesions[0] == 2

    def test_persist_bag_details(self, temp_db, sample_propagator):
        """Test that bag details are correctly persisted."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

            # Query B1
            result = db.conn.execute(
                "SELECT elements, phase FROM bags WHERE world_id = ? AND bag_id = ?",
                ["test_world", "B1"]
            ).fetchone()

            elements = set(json.loads(result[0]))
            assert elements == {1, 2, 3}
            assert result[1] == Phase.PHASE_1.value

    def test_persist_adhesion_details(self, temp_db, sample_propagator):
        """Test that adhesion details are correctly persisted."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

            # Query B1--B2 adhesion
            result = db.conn.execute(
                "SELECT overlap, phases FROM adhesions WHERE world_id = ? AND adhesion_id = ?",
                ["test_world", "B1--B2"]
            ).fetchone()

            overlap = set(json.loads(result[0]))
            phases = {Phase(p) for p in json.loads(result[1])}

            assert overlap == {2, 3}
            assert phases == {Phase.PHASE_1}

    def test_persist_local_data(self, temp_db, sample_propagator):
        """Test that local data is correctly persisted."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

            # Query B1 local data
            result = db.conn.execute(
                "SELECT value FROM bag_local_data WHERE world_id = ? AND bag_id = ? AND key = ?",
                ["test_world", "B1", "status"]
            ).fetchone()

            value = json.loads(result[0])
            assert value == "acquired"

    def test_load_propagator(self, temp_db, sample_propagator):
        """Test loading propagator from database."""
        with EdgePhaseDuckLake(temp_db) as db:
            # Persist
            db.persist_propagator("test_world", sample_propagator)

        # Load
        with EdgePhaseDuckLake(temp_db) as db:
            loaded = db.load_propagator("test_world")

            # Verify structure
            assert len(loaded.bags) == 3
            assert len(loaded.adhesions) == 2
            assert loaded.bags["B1"].elements == {1, 2, 3}

    def test_load_local_data(self, temp_db, sample_propagator):
        """Test that local data is correctly loaded."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

        with EdgePhaseDuckLake(temp_db) as db:
            loaded = db.load_propagator("test_world")

            # Check loaded data
            assert loaded.bags["B1"].local_data.get("status") == "acquired"
            assert loaded.bags["B3"].local_data.get("status") == "validated"

    def test_load_partial_phases(self, temp_db, sample_propagator):
        """Test loading propagator with only specific phases."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

        # Load only PHASE_1 and PHASE_2
        with EdgePhaseDuckLake(temp_db) as db:
            loaded = db.load_propagator(
                "test_world",
                phases=[Phase.PHASE_1, Phase.PHASE_2]
            )

            # Should load adhesions that span these phases
            assert len(loaded.adhesions) == 2
            assert all(
                all(p in loaded.phases for p in a.phases)
                for a in loaded.adhesions
            )

    def test_query_phase_edges(self, temp_db, sample_propagator):
        """Test querying edges in a specific phase."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

            # Query Phase 1 edges
            edges_p1 = db.query_phase_edges("test_world", Phase.PHASE_1)
            assert len(edges_p1) == 2

            # Query Phase 2 edges (only B2--B3 should have Phase 2)
            edges_p2 = db.query_phase_edges("test_world", Phase.PHASE_2)
            assert len(edges_p2) == 1
            assert edges_p2[0]["adhesion_id"] == "B2--B3"

    def test_query_edge_properties(self, temp_db, sample_propagator):
        """Test that edge properties are correctly stored and queried."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

            edges = db.query_phase_edges("test_world", Phase.PHASE_1)
            edge = edges[0]

            # Check edge properties
            assert "trit_color" in edge
            assert isinstance(edge["trit_color"], Trit)
            assert "satisfied" in edge
            assert "left_restrictions" in edge
            assert "right_restrictions" in edge

    def test_query_phase_state(self, temp_db, sample_propagator):
        """Test querying phase state."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

            state_p1 = db.query_phase_state("test_world", Phase.PHASE_1)

            assert "trit_sum" in state_p1
            assert "total_adhesions" in state_p1
            assert "gf3_conserved" in state_p1
            assert state_p1["total_adhesions"] == 2

    def test_query_bag_neighbors(self, temp_db, sample_propagator):
        """Test querying neighbors of a bag."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

            # Query neighbors of B2 in Phase 1
            neighbors = db.query_bag_neighbors("test_world", "B2", Phase.PHASE_1)

            # B2 is adjacent to B1 and B3 via adhesions
            neighbor_ids = {n["neighbor_id"] for n in neighbors}
            assert "B1" in neighbor_ids or "B3" in neighbor_ids

    def test_record_propagation(self, temp_db):
        """Test recording phase-to-phase propagation."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.record_propagation("test_world", Phase.PHASE_1, Phase.PHASE_2, 5)

            # Query recorded propagation
            prop_info = db.query_propagation_path("test_world", Phase.PHASE_1, Phase.PHASE_2)

            assert prop_info["exists"] == True
            assert prop_info["constraint_count"] == 5

    def test_get_world_summary(self, temp_db, sample_propagator):
        """Test getting world summary."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

            summary = db.get_world_summary("test_world")

            assert summary["world_id"] == "test_world"
            assert summary["total_bags"] == 3
            assert summary["total_adhesions"] == 2
            assert "phase_states" in summary

    def test_round_trip_persistence(self, temp_db, sample_propagator):
        """Test round-trip: persist, load, and verify equivalence."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

        with EdgePhaseDuckLake(temp_db) as db:
            loaded = db.load_propagator("test_world")

            # Verify structure
            assert len(loaded.bags) == len(sample_propagator.bags)
            assert len(loaded.adhesions) == len(sample_propagator.adhesions)

            # Verify bag details
            for bag_id in sample_propagator.bags:
                assert loaded.bags[bag_id].elements == sample_propagator.bags[bag_id].elements
                assert loaded.bags[bag_id].phase == sample_propagator.bags[bag_id].phase

            # Verify adhesion details
            for i, adhesion in enumerate(sample_propagator.adhesions):
                loaded_adhesion = loaded.adhesions[i]
                assert loaded_adhesion.overlap == adhesion.overlap
                assert loaded_adhesion.phases == adhesion.phases

    def test_multiple_worlds(self, temp_db):
        """Test storing multiple independent worlds."""
        # Create two different propagators
        prop1 = EdgePhasePropagatorScoped(phases=[Phase.PHASE_1, Phase.PHASE_2])
        prop1.add_bag(Bag(id="A1", elements={1, 2}))
        prop1.add_bag(Bag(id="A2", elements={2, 3}))
        prop1.add_adhesion("A1", "A2", phases={Phase.PHASE_1})

        prop2 = EdgePhasePropagatorScoped(phases=[Phase.PHASE_1])
        prop2.add_bag(Bag(id="B1", elements={4, 5}))
        prop2.add_bag(Bag(id="B2", elements={5, 6}))
        prop2.add_adhesion("B1", "B2", phases={Phase.PHASE_1})

        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("world_1", prop1)
            db.persist_propagator("world_2", prop2)

            # Query each world separately
            summary1 = db.get_world_summary("world_1")
            summary2 = db.get_world_summary("world_2")

            assert summary1["total_bags"] == 2
            assert summary2["total_bags"] == 2
            assert summary1["world_id"] == "world_1"
            assert summary2["world_id"] == "world_2"

    def test_update_propagator(self, temp_db, sample_propagator):
        """Test updating persisted propagator."""
        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

        # Modify propagator
        sample_propagator.set_local_data("B1", "new_field", "new_value", Phase.PHASE_1)

        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("test_world", sample_propagator)

            # Verify update
            loaded = db.load_propagator("test_world")
            assert loaded.bags["B1"].local_data.get("new_field") == "new_value"

    def test_empty_world(self, temp_db):
        """Test handling empty propagator."""
        prop = EdgePhasePropagatorScoped(phases=[Phase.PHASE_1])

        with EdgePhaseDuckLake(temp_db) as db:
            db.persist_propagator("empty_world", prop)

            summary = db.get_world_summary("empty_world")
            assert summary["total_bags"] == 0
            assert summary["total_adhesions"] == 0

    def test_context_manager(self, temp_db):
        """Test using DuckLake as context manager."""
        with EdgePhaseDuckLake(temp_db) as db:
            tables = db.conn.execute(
                "SELECT COUNT(*) FROM duckdb_tables()"
            ).fetchone()
            assert tables[0] > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
