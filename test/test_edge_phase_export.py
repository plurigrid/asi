#!/usr/bin/env python3
"""
Test suite for Edge Phase Exporter

Tests multi-format export with phase tracking and verification.
"""

import sys
import json
import tempfile
from pathlib import Path

sys.path.insert(0, '../lib')

from edge_phase_propagator_scoped import (
    EdgePhasePropagatorScoped, Bag, Phase, Trit
)
from edge_phase_ducklake import EdgePhaseDuckLake
from edge_phase_export import EdgePhaseExporter, ExportResult


class TestEdgePhaseExport:
    """Test export functionality."""

    @staticmethod
    def setup_test_propagator(db_path: str) -> str:
        """Create and persist test propagator."""
        prop = EdgePhasePropagatorScoped(
            phases=[Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3]
        )

        prop.add_bag(Bag(id="B1", elements={1, 2, 3}, phase=Phase.PHASE_1))
        prop.add_bag(Bag(id="B2", elements={2, 3, 4}, phase=Phase.PHASE_2))
        prop.add_bag(Bag(id="B3", elements={3, 4, 5}, phase=Phase.PHASE_3))

        prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1, Phase.PHASE_2})
        prop.add_adhesion("B2", "B3", phases={Phase.PHASE_2, Phase.PHASE_3})

        prop.set_local_data("B1", "source", "sensor", Phase.PHASE_1)
        prop.set_local_data("B2", "validated", True, Phase.PHASE_2)
        prop.set_local_data("B3", "deployed", True, Phase.PHASE_3)

        with EdgePhaseDuckLake(db_path) as db:
            db.persist_propagator("test_export", prop)

        return "test_export"

    def test_export_result_creation(self):
        """Test creating valid export results."""
        result = ExportResult(
            world_id="test",
            export_format="json",
            phases_applied=[Phase.PHASE_1],
            timestamp="2025-12-26",
            gf3_conserved=True,
            total_bags=2,
            total_adhesions=1,
            total_edges=1,
            json_content="{}"
        )

        assert result.world_id == "test"
        assert result.gf3_conserved == True
        assert result.total_bags == 2

    def test_export_result_validation(self):
        """Test export result validation."""
        # Valid result
        result = ExportResult(
            world_id="test",
            export_format="json",
            phases_applied=[Phase.PHASE_1],
            timestamp="2025-12-26",
            gf3_conserved=True,
            total_bags=2,
            total_adhesions=1,
            total_edges=1
        )
        assert result is not None

        # Invalid: no phases
        try:
            ExportResult(
                world_id="test",
                export_format="json",
                phases_applied=[],
                timestamp="2025-12-26",
                gf3_conserved=True,
                total_bags=2,
                total_adhesions=1,
                total_edges=1
            )
            assert False, "Should reject empty phases"
        except ValueError:
            pass  # Expected

    def test_json_export(self):
        """Test JSON format export."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        try:
            world_id = self.setup_test_propagator(db_path)

            exporter = EdgePhaseExporter(db_path)
            result = exporter.export_json(
                world_id,
                phases=[Phase.PHASE_1, Phase.PHASE_2]
            )

            # Verify structure
            assert result.export_format == "json"
            assert result.json_content is not None
            assert len(result.json_content) > 0

            # Parse JSON
            data = json.loads(result.json_content)
            assert "metadata" in data
            assert "bags" in data
            assert "adhesions" in data
            assert "phase_states" in data

            # Check metadata
            assert data["metadata"]["world_id"] == world_id
            assert "PHASE_1" in data["metadata"]["phases_applied"]
            assert "PHASE_2" in data["metadata"]["phases_applied"]

            # Check bags
            assert "B1" in data["bags"]
            assert set(data["bags"]["B1"]["elements"]) == {1, 2, 3}

        finally:
            Path(db_path).unlink(missing_ok=True)

    def test_sexp_export(self):
        """Test S-expression format export."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        try:
            world_id = self.setup_test_propagator(db_path)

            exporter = EdgePhaseExporter(db_path)
            result = exporter.export_sexp(
                world_id,
                phases=[Phase.PHASE_1, Phase.PHASE_2]
            )

            # Verify structure
            assert result.export_format == "sexp"
            assert result.sexp_content is not None
            assert "edge-phase-propagator" in result.sexp_content
            assert "world-id" in result.sexp_content
            assert "bags" in result.sexp_content
            assert "adhesions" in result.sexp_content
            assert "phase-states" in result.sexp_content

            # Check content
            assert "B1" in result.sexp_content
            assert "B2" in result.sexp_content
            assert "PHASE_1" in result.sexp_content

        finally:
            Path(db_path).unlink(missing_ok=True)

    def test_gf3_export(self):
        """Test GF(3) notation export."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        try:
            world_id = self.setup_test_propagator(db_path)

            exporter = EdgePhaseExporter(db_path)
            result = exporter.export_gf3(
                world_id,
                phases=[Phase.PHASE_1, Phase.PHASE_2]
            )

            # Verify structure
            assert result.export_format == "gf3"
            assert result.gf3_content is not None
            assert "GF(3)" in result.gf3_content
            assert "PHASE STATES" in result.gf3_content
            assert "ADHESION COLORS" in result.gf3_content

            # Check symbols
            assert "⊖" in result.gf3_content or "⊙" in result.gf3_content or "⊕" in result.gf3_content

        finally:
            Path(db_path).unlink(missing_ok=True)

    def test_export_all_formats(self):
        """Test exporting all formats at once."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        try:
            world_id = self.setup_test_propagator(db_path)

            exporter = EdgePhaseExporter(db_path)
            all_results = exporter.export_all(
                world_id,
                phases=[Phase.PHASE_1, Phase.PHASE_2]
            )

            # Check all formats present
            assert "json" in all_results
            assert "sexp" in all_results
            assert "gf3" in all_results

            # Verify each
            assert all_results["json"].json_content is not None
            assert all_results["sexp"].sexp_content is not None
            assert all_results["gf3"].gf3_content is not None

            # All should have same metadata
            for result in all_results.values():
                assert result.world_id == world_id
                assert result.total_bags == 3
                assert result.total_adhesions == 2

        finally:
            Path(db_path).unlink(missing_ok=True)

    def test_export_gf3_conservation(self):
        """Test GF(3) conservation tracking in exports."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        try:
            world_id = self.setup_test_propagator(db_path)

            exporter = EdgePhaseExporter(db_path)
            result = exporter.export_json(world_id)

            # Check conservation status
            assert isinstance(result.gf3_conserved, bool)

            # Parse JSON and verify
            data = json.loads(result.json_content)
            for phase_name, phase_state in data["phase_states"].items():
                # Each phase should report conservation status
                assert "gf3_conserved" in phase_state

        finally:
            Path(db_path).unlink(missing_ok=True)

    def test_save_export(self):
        """Test saving export to files."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        with tempfile.TemporaryDirectory() as tmpdir:
            try:
                world_id = self.setup_test_propagator(db_path)

                exporter = EdgePhaseExporter(db_path)
                result = exporter.export_json(world_id)

                # Save to file
                saved = exporter.save_export(result, tmpdir)

                assert "json" in saved
                assert Path(saved["json"]).exists()

                # Verify file content
                with open(saved["json"]) as f:
                    data = json.load(f)
                    assert data["metadata"]["world_id"] == world_id

            finally:
                Path(db_path).unlink(missing_ok=True)

    def test_save_all_exports(self):
        """Test saving all export formats to files."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        with tempfile.TemporaryDirectory() as tmpdir:
            try:
                world_id = self.setup_test_propagator(db_path)

                exporter = EdgePhaseExporter(db_path)
                all_results = exporter.export_all(world_id)

                # Save all
                for format_name, result in all_results.items():
                    saved = exporter.save_export(result, tmpdir)
                    assert len(saved) > 0

                # Check files exist
                json_files = list(Path(tmpdir).glob("*.json"))
                lisp_files = list(Path(tmpdir).glob("*.lisp"))
                gf3_files = list(Path(tmpdir).glob("*.gf3"))

                assert len(json_files) > 0
                assert len(lisp_files) > 0
                assert len(gf3_files) > 0

            finally:
                Path(db_path).unlink(missing_ok=True)

    def test_verify_valid_export(self):
        """Test verifying a valid export."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        try:
            world_id = self.setup_test_propagator(db_path)

            exporter = EdgePhaseExporter(db_path)
            result = exporter.export_json(world_id)

            # Verify
            valid, errors = exporter.verify_export(result)

            assert valid == True
            assert len(errors) == 0

        finally:
            Path(db_path).unlink(missing_ok=True)

    def test_verify_invalid_export(self):
        """Test verifying an invalid export."""
        # Create invalid result
        result = ExportResult(
            world_id="test",
            export_format="json",
            phases_applied=[Phase.PHASE_1],
            timestamp="2025-12-26",
            gf3_conserved=False,  # Not conserved
            total_bags=0,  # No bags
            total_adhesions=0,
            total_edges=0,
            json_content=None  # No content
        )

        exporter = EdgePhaseExporter()
        valid, errors = exporter.verify_export(result)

        assert valid == False
        assert len(errors) > 0
        assert any("GF(3)" in e for e in errors)
        assert any("bags" in e for e in errors)

    def test_export_phase_filtering(self):
        """Test exporting only specific phases."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        try:
            world_id = self.setup_test_propagator(db_path)

            exporter = EdgePhaseExporter(db_path)

            # Export only Phase 1
            result_p1 = exporter.export_json(world_id, phases=[Phase.PHASE_1])
            data_p1 = json.loads(result_p1.json_content)

            # Export Phase 1 and 2
            result_p12 = exporter.export_json(
                world_id,
                phases=[Phase.PHASE_1, Phase.PHASE_2]
            )
            data_p12 = json.loads(result_p12.json_content)

            # Phase 1 only should have fewer phases
            assert len(result_p1.phases_applied) == 1
            assert len(result_p12.phases_applied) == 2

            # Both should have same bags but different edges
            assert data_p1["metadata"]["phases_applied"] == ["PHASE_1"]
            assert "PHASE_1" in data_p12["metadata"]["phases_applied"]
            assert "PHASE_2" in data_p12["metadata"]["phases_applied"]

        finally:
            Path(db_path).unlink(missing_ok=True)

    def test_export_metadata_completeness(self):
        """Test that exports contain all required metadata."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        try:
            world_id = self.setup_test_propagator(db_path)

            exporter = EdgePhaseExporter(db_path)
            result = exporter.export_json(world_id)

            # Check result metadata
            assert result.world_id is not None
            assert result.export_format is not None
            assert result.phases_applied is not None
            assert result.timestamp is not None
            assert result.gf3_conserved is not None
            assert result.total_bags > 0
            assert result.total_adhesions >= 0
            assert result.total_edges >= 0

        finally:
            Path(db_path).unlink(missing_ok=True)

    def test_round_trip_json_export(self):
        """Test that exported JSON can be parsed and validated."""
        with tempfile.NamedTemporaryFile(suffix='.duckdb', delete=False) as f:
            db_path = f.name

        try:
            world_id = self.setup_test_propagator(db_path)

            exporter = EdgePhaseExporter(db_path)
            result = exporter.export_json(world_id)

            # Parse exported JSON
            data = json.loads(result.json_content)

            # Validate structure
            assert data["metadata"]["world_id"] == result.world_id
            assert len(data["bags"]) == result.total_bags
            assert len(data["adhesions"]) == result.total_adhesions

            # Validate bags
            for bag_id, bag_data in data["bags"].items():
                assert "id" in bag_data
                assert "elements" in bag_data
                assert "phase" in bag_data

            # Validate adhesions
            for adhesion_data in data["adhesions"]:
                assert "id" in adhesion_data
                assert "left_bag" in adhesion_data
                assert "right_bag" in adhesion_data
                assert "overlap" in adhesion_data

        finally:
            Path(db_path).unlink(missing_ok=True)


if __name__ == "__main__":
    import pytest
    pytest.main([__file__, "-v"])
