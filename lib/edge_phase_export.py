#!/usr/bin/env python3
"""
Edge Phase Propagator - Export Procedures
Integration between EdgePhasePropagatorScoped and export formats

Provides:
- Multi-format export (JSON, S-expression, GF(3) notation)
- Phase metadata tracking
- GF(3) conservation verification
- Reversible serialization
"""

import json
from typing import Dict, Any, List, Optional, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime

from edge_phase_propagator_scoped import (
    EdgePhasePropagatorScoped, Bag, Adhesion, Phase, Trit
)
from edge_phase_ducklake import EdgePhaseDuckLake


@dataclass
class ExportResult:
    """Result of exporting a propagator."""
    world_id: str
    export_format: str  # "json", "sexp", "gf3", "mixed"
    phases_applied: List[Phase]
    timestamp: str
    gf3_conserved: bool
    total_bags: int
    total_adhesions: int
    total_edges: int

    # Format-specific content
    json_content: Optional[str] = None
    sexp_content: Optional[str] = None
    gf3_content: Optional[str] = None

    def __post_init__(self):
        """Validate export result."""
        if not self.phases_applied:
            raise ValueError("Must apply at least one phase")
        if self.total_bags < 0 or self.total_adhesions < 0:
            raise ValueError("Invalid counts")


class EdgePhaseExporter:
    """
    Export propagator state in multiple formats with phase tracking.

    Handles:
    - JSON export (complete state)
    - S-expression export (lisp-like notation)
    - GF(3) notation (balanced ternary representation)
    - Phase metadata preservation
    - Conservation verification
    """

    def __init__(self, db_path: str = "/Users/bob/ies/plurigrid/asi/lib/edge_phase.duckdb"):
        """Initialize exporter with database connection."""
        self.db_path = db_path

    def export_json(self, world_id: str, phases: Optional[List[Phase]] = None) -> ExportResult:
        """
        Export propagator as JSON with complete metadata.

        Returns ExportResult with json_content field populated.
        """
        with EdgePhaseDuckLake(self.db_path) as db:
            # Load propagator
            prop = db.load_propagator(world_id, phases=phases)

            # Determine which phases were actually applied
            applied_phases = phases or prop.phases

            # Build JSON structure
            export_data = {
                "metadata": {
                    "world_id": world_id,
                    "export_format": "json",
                    "timestamp": datetime.now().isoformat(),
                    "phases_applied": [p.name for p in applied_phases],
                    "phase_count": len(applied_phases)
                },
                "bags": {},
                "adhesions": [],
                "phase_states": {}
            }

            # Export bags
            for bag_id, bag in prop.bags.items():
                export_data["bags"][bag_id] = {
                    "id": bag.id,
                    "elements": sorted(list(bag.elements)),
                    "phase": bag.phase.name,
                    "trit_phase": bag.trit_phase.name,
                    "local_data": {
                        k: v for k, v in bag.local_data.items()
                    }
                }

            # Export adhesions
            for adhesion in prop.adhesions:
                adhesion_data = {
                    "id": adhesion.id,
                    "left_bag": adhesion.left_bag.id,
                    "right_bag": adhesion.right_bag.id,
                    "overlap": sorted(list(adhesion.overlap)),
                    "phases": [p.name for p in adhesion.phases],
                    "per_phase": {}
                }

                # Per-phase data
                for phase in adhesion.phases:
                    if phase in applied_phases or not phases:
                        adhesion_data["per_phase"][phase.name] = {
                            "trit_color": adhesion.trit_colors[phase].name,
                            "left_restrictions": adhesion.left_restrictions.get(phase, {}),
                            "right_restrictions": adhesion.right_restrictions.get(phase, {})
                        }

                export_data["adhesions"].append(adhesion_data)

            # Export phase states
            for phase in applied_phases:
                export_data["phase_states"][phase.name] = {
                    "trit_sum": prop._trit_sums[phase].name,
                    "gf3_conserved": prop.verify_gf3_conservation(phase),
                    "total_adhesions": len([a for a in prop.adhesions if phase in a.phases])
                }

            # Create result
            json_str = json.dumps(export_data, indent=2)

            return ExportResult(
                world_id=world_id,
                export_format="json",
                phases_applied=applied_phases,
                timestamp=datetime.now().isoformat(),
                gf3_conserved=all(
                    prop.verify_gf3_conservation(p) for p in applied_phases
                ),
                total_bags=len(prop.bags),
                total_adhesions=len(prop.adhesions),
                total_edges=sum(
                    len([a for a in prop.adhesions if p in a.phases])
                    for p in applied_phases
                ),
                json_content=json_str
            )

    def export_sexp(self, world_id: str, phases: Optional[List[Phase]] = None) -> ExportResult:
        """
        Export propagator as S-expression (Lisp-like notation).

        Returns ExportResult with sexp_content field populated.
        """
        with EdgePhaseDuckLake(self.db_path) as db:
            prop = db.load_propagator(world_id, phases=phases)
            applied_phases = phases or prop.phases

            lines = []
            lines.append("(edge-phase-propagator")
            lines.append(f"  (world-id \"{world_id}\")")
            lines.append(f"  (phases {' '.join(p.name for p in applied_phases)})")
            lines.append(f"  (timestamp \"{datetime.now().isoformat()}\")")

            # Bags
            lines.append("  (bags")
            for bag_id, bag in prop.bags.items():
                elements_str = " ".join(str(e) for e in sorted(bag.elements))
                lines.append(f"    (bag \"{bag_id}\"")
                lines.append(f"      (elements {elements_str})")
                lines.append(f"      (phase {bag.phase.name})")
                lines.append(f"      (trit {bag.trit_phase.name})")

                if bag.local_data:
                    lines.append("      (data")
                    for key, value in bag.local_data.items():
                        lines.append(f"        (\"{key}\" {json.dumps(value)})")
                    lines.append("      )")
                lines.append("    )")
            lines.append("  )")

            # Adhesions
            lines.append("  (adhesions")
            for adhesion in prop.adhesions:
                overlap_str = " ".join(str(e) for e in sorted(adhesion.overlap))
                lines.append(f"    (adhesion \"{adhesion.id}\"")
                lines.append(f"      (left \"{adhesion.left_bag.id}\")")
                lines.append(f"      (right \"{adhesion.right_bag.id}\")")
                lines.append(f"      (overlap {overlap_str})")

                for phase in adhesion.phases:
                    if phase in applied_phases or not phases:
                        lines.append(f"      (phase {phase.name}")
                        lines.append(f"        (trit {adhesion.trit_colors[phase].name})")
                        lines.append("      )")

                lines.append("    )")
            lines.append("  )")

            # Phase states
            lines.append("  (phase-states")
            for phase in applied_phases:
                conserved = "true" if prop.verify_gf3_conservation(phase) else "false"
                lines.append(f"    ({phase.name}")
                lines.append(f"      (trit-sum {prop._trit_sums[phase].name})")
                lines.append(f"      (gf3-conserved {conserved})")
                lines.append("    )")
            lines.append("  )")

            lines.append(")")

            sexp_str = "\n".join(lines)

            return ExportResult(
                world_id=world_id,
                export_format="sexp",
                phases_applied=applied_phases,
                timestamp=datetime.now().isoformat(),
                gf3_conserved=all(
                    prop.verify_gf3_conservation(p) for p in applied_phases
                ),
                total_bags=len(prop.bags),
                total_adhesions=len(prop.adhesions),
                total_edges=sum(
                    len([a for a in prop.adhesions if p in a.phases])
                    for p in applied_phases
                ),
                sexp_content=sexp_str
            )

    def export_gf3(self, world_id: str, phases: Optional[List[Phase]] = None) -> ExportResult:
        """
        Export propagator in GF(3) notation (balanced ternary).

        Returns ExportResult with gf3_content field populated.
        """
        with EdgePhaseDuckLake(self.db_path) as db:
            prop = db.load_propagator(world_id, phases=phases)
            applied_phases = phases or prop.phases

            lines = []
            lines.append("GF(3) EDGE PHASE EXPORT")
            lines.append("=" * 50)
            lines.append(f"World: {world_id}")
            lines.append(f"Timestamp: {datetime.now().isoformat()}")
            lines.append(f"Phases: {', '.join(p.name for p in applied_phases)}")
            lines.append("")

            # Phase states
            lines.append("PHASE STATES (GF(3) Sums)")
            lines.append("-" * 50)
            for phase in applied_phases:
                trit_sum = prop._trit_sums[phase]
                conserved = "✓" if prop.verify_gf3_conservation(phase) else "✗"
                trit_symbol = {
                    Trit.MINUS: "⊖",
                    Trit.ZERO: "⊙",
                    Trit.PLUS: "⊕"
                }.get(trit_sum, "?")

                lines.append(f"{phase.name:8} : {trit_symbol} {trit_sum.name:5} {conserved}")
            lines.append("")

            # Adhesion colors per phase
            lines.append("ADHESION COLORS (Per-Phase)")
            lines.append("-" * 50)
            for phase in applied_phases:
                lines.append(f"\n{phase.name}:")
                for adhesion in prop.adhesions:
                    if phase in adhesion.phases:
                        color = adhesion.trit_colors[phase]
                        symbol = {
                            Trit.MINUS: "⊖",
                            Trit.ZERO: "⊙",
                            Trit.PLUS: "⊕"
                        }.get(color, "?")
                        lines.append(f"  {adhesion.id:15} : {symbol} {color.name}")
            lines.append("")

            # Summary
            lines.append("SUMMARY")
            lines.append("-" * 50)
            lines.append(f"Total bags: {len(prop.bags)}")
            lines.append(f"Total adhesions: {len(prop.adhesions)}")

            for phase in applied_phases:
                phase_edges = len([a for a in prop.adhesions if phase in a.phases])
                lines.append(f"  {phase.name}: {phase_edges} edges")

            lines.append("")

            # GF(3) balance check
            lines.append("GF(3) BALANCE CHECK")
            lines.append("-" * 50)
            all_conserved = all(prop.verify_gf3_conservation(p) for p in applied_phases)
            if all_conserved:
                lines.append("✓ ALL PHASES GF(3)-BALANCED")
            else:
                lines.append("✗ SOME PHASES NOT BALANCED")
                for phase in applied_phases:
                    if not prop.verify_gf3_conservation(phase):
                        lines.append(f"  {phase.name}: SUM = {prop._trit_sums[phase].name}")

            gf3_str = "\n".join(lines)

            return ExportResult(
                world_id=world_id,
                export_format="gf3",
                phases_applied=applied_phases,
                timestamp=datetime.now().isoformat(),
                gf3_conserved=all_conserved,
                total_bags=len(prop.bags),
                total_adhesions=len(prop.adhesions),
                total_edges=sum(
                    len([a for a in prop.adhesions if p in a.phases])
                    for p in applied_phases
                ),
                gf3_content=gf3_str
            )

    def export_all(self, world_id: str, phases: Optional[List[Phase]] = None) -> Dict[str, ExportResult]:
        """
        Export propagator in all formats.

        Returns dictionary with keys: 'json', 'sexp', 'gf3'
        """
        return {
            "json": self.export_json(world_id, phases),
            "sexp": self.export_sexp(world_id, phases),
            "gf3": self.export_gf3(world_id, phases)
        }

    def save_export(self, result: ExportResult, output_dir: str = "/tmp") -> Dict[str, str]:
        """
        Save export result to files.

        Returns dictionary of {format: filepath}
        """
        import os
        os.makedirs(output_dir, exist_ok=True)

        saved_files = {}

        if result.json_content:
            filepath = f"{output_dir}/{result.world_id}.json"
            with open(filepath, 'w') as f:
                f.write(result.json_content)
            saved_files['json'] = filepath

        if result.sexp_content:
            filepath = f"{output_dir}/{result.world_id}.lisp"
            with open(filepath, 'w') as f:
                f.write(result.sexp_content)
            saved_files['sexp'] = filepath

        if result.gf3_content:
            filepath = f"{output_dir}/{result.world_id}.gf3"
            with open(filepath, 'w') as f:
                f.write(result.gf3_content)
            saved_files['gf3'] = filepath

        return saved_files

    def verify_export(self, result: ExportResult) -> Tuple[bool, List[str]]:
        """
        Verify export result integrity.

        Returns: (is_valid, list_of_errors)
        """
        errors = []

        # Check GF(3) conservation
        if not result.gf3_conserved:
            errors.append(f"GF(3) not conserved across phases {result.phases_applied}")

        # Check counts
        if result.total_bags <= 0:
            errors.append("No bags in export")

        if result.total_adhesions < 0:
            errors.append("Invalid adhesion count")

        # Check content exists
        if result.export_format in ['json', 'all'] and not result.json_content:
            errors.append("JSON content missing")

        if result.export_format in ['sexp', 'all'] and not result.sexp_content:
            errors.append("S-expression content missing")

        if result.export_format in ['gf3', 'all'] and not result.gf3_content:
            errors.append("GF(3) content missing")

        return len(errors) == 0, errors


def demo():
    """Demonstrate export functionality."""
    from edge_phase_propagator_scoped import EdgePhasePropagatorScoped, Bag
    from edge_phase_ducklake import EdgePhaseDuckLake

    print("Edge Phase Exporter Demo")
    print("=" * 60)

    # Create and persist propagator
    prop = EdgePhasePropagatorScoped(phases=[Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3])
    prop.add_bag(Bag(id="B1", elements={1, 2, 3}, phase=Phase.PHASE_1))
    prop.add_bag(Bag(id="B2", elements={2, 3, 4}, phase=Phase.PHASE_2))
    prop.add_bag(Bag(id="B3", elements={3, 4, 5}, phase=Phase.PHASE_3))

    prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1, Phase.PHASE_2})
    prop.add_adhesion("B2", "B3", phases={Phase.PHASE_2, Phase.PHASE_3})

    prop.set_local_data("B1", "source", "sensor_A", Phase.PHASE_1)
    prop.set_local_data("B2", "validated", True, Phase.PHASE_2)
    prop.set_local_data("B3", "deployed", True, Phase.PHASE_3)

    print("\n1. Persisting propagator...")
    with EdgePhaseDuckLake() as db:
        db.persist_propagator("export_demo", prop)
    print("   ✅ Persisted")

    # Export in all formats
    print("\n2. Exporting in all formats...")
    exporter = EdgePhaseExporter()

    json_result = exporter.export_json("export_demo", phases=[Phase.PHASE_1, Phase.PHASE_2])
    print(f"   ✅ JSON export: {len(json_result.json_content)} chars")

    sexp_result = exporter.export_sexp("export_demo", phases=[Phase.PHASE_1, Phase.PHASE_2])
    print(f"   ✅ S-expression export: {len(sexp_result.sexp_content)} chars")

    gf3_result = exporter.export_gf3("export_demo", phases=[Phase.PHASE_1, Phase.PHASE_2])
    print(f"   ✅ GF(3) export: {len(gf3_result.gf3_content)} chars")

    # Verify exports
    print("\n3. Verifying exports...")
    for name, result in [("JSON", json_result), ("SEXP", sexp_result), ("GF(3)", gf3_result)]:
        valid, errors = exporter.verify_export(result)
        status = "✅" if valid else "❌"
        print(f"   {status} {name}: GF(3)={result.gf3_conserved}, bags={result.total_bags}, edges={result.total_edges}")
        if errors:
            for error in errors:
                print(f"      - {error}")

    # Print GF(3) export
    print("\n4. GF(3) Export Preview:")
    print("-" * 60)
    print(gf3_result.gf3_content)


if __name__ == "__main__":
    demo()
