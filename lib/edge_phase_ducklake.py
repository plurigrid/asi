#!/usr/bin/env python3
"""
Edge Phase Propagator - DuckLake Persistence Layer
Integration between EdgePhasePropagatorScoped and DuckLake backend

Provides:
- Database schema creation
- Persistence of phase-scoped edge states
- Querying and loading edge graphs from database
- Real-time synchronization with DuckLake
"""

import duckdb
import json
from typing import Optional, Dict, List, Any
from dataclasses import asdict
from pathlib import Path

from edge_phase_propagator_scoped import (
    EdgePhasePropagatorScoped, Bag, Adhesion, EdgePhaseState,
    Phase, Trit
)


class EdgePhaseDuckLake:
    """
    Persistence layer for Edge Phase Propagator using DuckLake backend.

    Manages:
    - Schema creation and migration
    - Storing phase-scoped edge states
    - Loading edge graphs from database
    - Querying relationships and constraints
    - Real-time sync with propagator
    """

    def __init__(self, db_path: str = "/Users/bob/ies/plurigrid/asi/lib/edge_phase.duckdb"):
        """Initialize DuckLake connection and ensure schema exists."""
        self.db_path = db_path
        self.conn = duckdb.connect(db_path)
        self._create_schema()

    def _create_schema(self) -> None:
        """Create database schema for phase-scoped edges."""

        # Main table for bags (nodes in tree decomposition)
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS bags (
                world_id TEXT NOT NULL,
                bag_id TEXT NOT NULL,
                elements TEXT NOT NULL,  -- JSON array
                phase INT NOT NULL,       -- Phase enum value
                trit_phase INT NOT NULL,  -- GF(3) trit value
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (world_id, bag_id)
            )
        """)

        # Main table for adhesions (edges between bags)
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS adhesions (
                world_id TEXT NOT NULL,
                adhesion_id TEXT NOT NULL,
                left_bag TEXT NOT NULL,
                right_bag TEXT NOT NULL,
                overlap TEXT NOT NULL,  -- JSON array
                phases TEXT NOT NULL,    -- JSON array of phase integers
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (world_id, adhesion_id),
                FOREIGN KEY (world_id, left_bag) REFERENCES bags(world_id, bag_id),
                FOREIGN KEY (world_id, right_bag) REFERENCES bags(world_id, bag_id)
            )
        """)

        # Per-phase edge states
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS phase_edges (
                world_id TEXT NOT NULL,
                phase INT NOT NULL,
                adhesion_id TEXT NOT NULL,
                trit_color INT NOT NULL,  -- GF(3) color per phase
                is_filtered BOOLEAN DEFAULT FALSE,
                pullback_elements TEXT,    -- JSON array
                satisfied BOOLEAN DEFAULT TRUE,
                left_restrictions TEXT,    -- JSON object
                right_restrictions TEXT,   -- JSON object
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (world_id, phase, adhesion_id),
                FOREIGN KEY (world_id, adhesion_id) REFERENCES adhesions(world_id, adhesion_id)
            )
        """)

        # Phase state tracking
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS phase_states (
                world_id TEXT NOT NULL,
                phase INT NOT NULL,
                trit_sum INT NOT NULL,  -- GF(3) sum for phase
                total_adhesions INT DEFAULT 0,
                sheaf_satisfiable BOOLEAN DEFAULT TRUE,
                gf3_conserved BOOLEAN DEFAULT TRUE,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (world_id, phase)
            )
        """)

        # Local data on bags
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS bag_local_data (
                world_id TEXT NOT NULL,
                bag_id TEXT NOT NULL,
                phase INT NOT NULL,
                key TEXT NOT NULL,
                value TEXT NOT NULL,  -- JSON-serialized value
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (world_id, bag_id, phase, key),
                FOREIGN KEY (world_id, bag_id) REFERENCES bags(world_id, bag_id)
            )
        """)

        # Phase dependency tracking
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS phase_dependencies (
                world_id TEXT NOT NULL,
                source_phase INT NOT NULL,
                target_phase INT NOT NULL,
                constraint_count INT DEFAULT 0,
                propagated_at TIMESTAMP,
                PRIMARY KEY (world_id, source_phase, target_phase)
            )
        """)

    def persist_propagator(self, world_id: str, propagator: EdgePhasePropagatorScoped) -> None:
        """Persist entire propagator state to DuckLake."""

        # Store bags
        for bag_id, bag in propagator.bags.items():
            self.conn.execute("""
                INSERT OR REPLACE INTO bags
                (world_id, bag_id, elements, phase, trit_phase)
                VALUES (?, ?, ?, ?, ?)
            """, [
                world_id,
                bag_id,
                json.dumps(sorted(list(bag.elements))),
                bag.phase.value,
                bag.trit_phase.value
            ])

            # Store local data for all phases
            for phase in propagator.phases:
                for key, value in bag.local_data.items():
                    self.conn.execute("""
                        INSERT OR REPLACE INTO bag_local_data
                        (world_id, bag_id, phase, key, value)
                        VALUES (?, ?, ?, ?, ?)
                    """, [
                        world_id,
                        bag_id,
                        phase.value,
                        key,
                        json.dumps(value)
                    ])

        # Store adhesions
        for adhesion in propagator.adhesions:
            adhesion_id = adhesion.id

            self.conn.execute("""
                INSERT OR REPLACE INTO adhesions
                (world_id, adhesion_id, left_bag, right_bag, overlap, phases)
                VALUES (?, ?, ?, ?, ?, ?)
            """, [
                world_id,
                adhesion_id,
                adhesion.left_bag.id,
                adhesion.right_bag.id,
                json.dumps(sorted(list(adhesion.overlap))),
                json.dumps([p.value for p in adhesion.phases])
            ])

            # Store per-phase edge state
            for phase in adhesion.phases:
                state = propagator.phase_edge_states[phase].get(adhesion.phase_id(phase))

                self.conn.execute("""
                    INSERT OR REPLACE INTO phase_edges
                    (world_id, phase, adhesion_id, trit_color, is_filtered,
                     pullback_elements, satisfied, left_restrictions, right_restrictions)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, [
                    world_id,
                    phase.value,
                    adhesion_id,
                    adhesion.trit_colors[phase].value,
                    state.is_filtered if state else False,
                    json.dumps(sorted(list(state.pullback_elements))) if state and state.pullback_elements else None,
                    state.satisfied if state else True,
                    json.dumps(adhesion.left_restrictions.get(phase, {})),
                    json.dumps(adhesion.right_restrictions.get(phase, {}))
                ])

        # Store phase states
        for phase in propagator.phases:
            self.conn.execute("""
                INSERT OR REPLACE INTO phase_states
                (world_id, phase, trit_sum, total_adhesions, gf3_conserved)
                VALUES (?, ?, ?, ?, ?)
            """, [
                world_id,
                phase.value,
                propagator._trit_sums[phase].value,
                len([a for a in propagator.adhesions if phase in a.phases]),
                propagator.verify_gf3_conservation(phase)
            ])

        self.conn.commit()

    def load_propagator(self, world_id: str, phases: Optional[List[Phase]] = None) -> EdgePhasePropagatorScoped:
        """Load propagator state from DuckLake."""

        # Determine phases to load
        phases_to_load = phases or [Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3, Phase.PHASE_4]

        # Create propagator
        propagator = EdgePhasePropagatorScoped(phases=phases_to_load)

        # Load bags
        bags_result = self.conn.execute("""
            SELECT bag_id, elements, phase, trit_phase
            FROM bags
            WHERE world_id = ?
        """, [world_id]).fetchall()

        for bag_id, elements_json, phase_val, trit_val in bags_result:
            elements = set(json.loads(elements_json))
            bag = Bag(
                id=bag_id,
                elements=elements,
                phase=Phase(phase_val),
                trit_phase=Trit(trit_val)
            )
            propagator.add_bag(bag)

        # Load adhesions
        adhesions_result = self.conn.execute("""
            SELECT adhesion_id, left_bag, right_bag, overlap, phases
            FROM adhesions
            WHERE world_id = ?
        """, [world_id]).fetchall()

        for adhesion_id, left_id, right_id, overlap_json, phases_json in adhesions_result:
            phases_set = {Phase(p) for p in json.loads(phases_json)}

            # Only add adhesion if all phases are loaded
            if phases_set.issubset(set(phases_to_load)):
                propagator.add_adhesion(left_id, right_id, phases=phases_set)

        # Load local data
        data_result = self.conn.execute("""
            SELECT bag_id, phase, key, value
            FROM bag_local_data
            WHERE world_id = ?
        """, [world_id]).fetchall()

        for bag_id, phase_val, key, value_json in data_result:
            phase = Phase(phase_val)
            value = json.loads(value_json)
            propagator.set_local_data(bag_id, key, value, phase)

        return propagator

    def query_phase_edges(self, world_id: str, phase: Phase) -> List[Dict[str, Any]]:
        """Query all edges in a specific phase."""
        result = self.conn.execute("""
            SELECT adhesion_id, trit_color, is_filtered, satisfied,
                   left_restrictions, right_restrictions
            FROM phase_edges
            WHERE world_id = ? AND phase = ?
            ORDER BY adhesion_id
        """, [world_id, phase.value]).fetchall()

        return [
            {
                "adhesion_id": row[0],
                "trit_color": Trit(row[1]),
                "is_filtered": row[2],
                "satisfied": row[3],
                "left_restrictions": json.loads(row[4]) if row[4] else {},
                "right_restrictions": json.loads(row[5]) if row[5] else {}
            }
            for row in result
        ]

    def query_phase_state(self, world_id: str, phase: Phase) -> Dict[str, Any]:
        """Query overall state for a phase."""
        result = self.conn.execute("""
            SELECT trit_sum, total_adhesions, sheaf_satisfiable, gf3_conserved
            FROM phase_states
            WHERE world_id = ? AND phase = ?
        """, [world_id, phase.value]).fetchone()

        if not result:
            return {}

        return {
            "trit_sum": Trit(result[0]),
            "total_adhesions": result[1],
            "sheaf_satisfiable": result[2],
            "gf3_conserved": result[3]
        }

    def query_bag_neighbors(self, world_id: str, bag_id: str, phase: Phase) -> List[Dict[str, Any]]:
        """Find all bags adjacent to given bag in a phase via adhesions."""
        result = self.conn.execute("""
            SELECT DISTINCT
                CASE
                    WHEN left_bag = ? THEN right_bag
                    ELSE left_bag
                END as neighbor_id,
                overlap
            FROM adhesions
            WHERE world_id = ? AND (left_bag = ? OR right_bag = ?)
              AND phases LIKE ?
        """, [
            bag_id, world_id, bag_id, bag_id,
            f'%{phase.value}%'
        ]).fetchall()

        return [
            {
                "neighbor_id": row[0],
                "overlap": set(json.loads(row[1]))
            }
            for row in result
        ]

    def query_propagation_path(self, world_id: str, source_phase: Phase, target_phase: Phase) -> Dict[str, Any]:
        """Query constraints propagated from source to target phase."""
        result = self.conn.execute("""
            SELECT source_phase, target_phase, constraint_count, propagated_at
            FROM phase_dependencies
            WHERE world_id = ? AND source_phase = ? AND target_phase = ?
        """, [world_id, source_phase.value, target_phase.value]).fetchone()

        if not result:
            return {"exists": False}

        return {
            "exists": True,
            "source_phase": Phase(result[0]),
            "target_phase": Phase(result[1]),
            "constraint_count": result[2],
            "propagated_at": result[3]
        }

    def record_propagation(self, world_id: str, source_phase: Phase, target_phase: Phase, constraint_count: int) -> None:
        """Record phase-to-phase constraint propagation."""
        self.conn.execute("""
            INSERT OR REPLACE INTO phase_dependencies
            (world_id, source_phase, target_phase, constraint_count, propagated_at)
            VALUES (?, ?, ?, ?, CURRENT_TIMESTAMP)
        """, [world_id, source_phase.value, target_phase.value, constraint_count])

        self.conn.commit()

    def get_world_summary(self, world_id: str) -> Dict[str, Any]:
        """Get complete summary of a world from database."""

        # Count bags and adhesions
        bags_count = self.conn.execute(
            "SELECT COUNT(*) FROM bags WHERE world_id = ?",
            [world_id]
        ).fetchone()[0]

        adhesions_count = self.conn.execute(
            "SELECT COUNT(*) FROM adhesions WHERE world_id = ?",
            [world_id]
        ).fetchone()[0]

        # Get phase states
        phase_states = {}
        phase_result = self.conn.execute(
            "SELECT phase, trit_sum, gf3_conserved FROM phase_states WHERE world_id = ?",
            [world_id]
        ).fetchall()

        for phase_val, trit_sum, conserved in phase_result:
            phase = Phase(phase_val)
            phase_states[f"Phase_{phase.value}"] = {
                "trit_sum": Trit(trit_sum),
                "gf3_conserved": conserved
            }

        return {
            "world_id": world_id,
            "total_bags": bags_count,
            "total_adhesions": adhesions_count,
            "phase_states": phase_states,
            "all_gf3_conserved": all(s["gf3_conserved"] for s in phase_states.values())
        }

    def close(self) -> None:
        """Close database connection."""
        self.conn.close()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()


def demo():
    """Demonstrate DuckLake integration."""
    print("Edge Phase Propagator - DuckLake Integration Demo")
    print("=" * 60)

    # Create propagator
    prop = EdgePhasePropagatorScoped(
        phases=[Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3]
    )

    # Build structure
    prop.add_bag(Bag(id="B1", elements={1, 2, 3}, phase=Phase.PHASE_1))
    prop.add_bag(Bag(id="B2", elements={2, 3, 4}, phase=Phase.PHASE_1))
    prop.add_bag(Bag(id="B3", elements={3, 4, 5}, phase=Phase.PHASE_2))

    prop.add_adhesion("B1", "B2", phases={Phase.PHASE_1})
    prop.add_adhesion("B2", "B3", phases={Phase.PHASE_1, Phase.PHASE_2})

    # Set data
    prop.set_local_data("B1", "status", "acquired", Phase.PHASE_1)
    prop.set_local_data("B2", "status", "acquired", Phase.PHASE_1)
    prop.set_local_data("B3", "status", "validated", Phase.PHASE_2)

    # Persist to DuckLake
    print("\n1. Persisting to DuckLake...")
    with EdgePhaseDuckLake() as db:
        db.persist_propagator("world_demo", prop)
        print("   ✅ Propagator persisted")

        # Query phase edges
        print("\n2. Querying Phase 1 edges...")
        edges_p1 = db.query_phase_edges("world_demo", Phase.PHASE_1)
        print(f"   Found {len(edges_p1)} edges")
        for edge in edges_p1:
            print(f"   - {edge['adhesion_id']}: trit={edge['trit_color'].name}, satisfied={edge['satisfied']}")

        # Query phase state
        print("\n3. Querying Phase 2 state...")
        state_p2 = db.query_phase_state("world_demo", Phase.PHASE_2)
        print(f"   GF(3) conserved: {state_p2['gf3_conserved']}")
        print(f"   Total adhesions: {state_p2['total_adhesions']}")

        # Get world summary
        print("\n4. World summary...")
        summary = db.get_world_summary("world_demo")
        print(f"   Bags: {summary['total_bags']}")
        print(f"   Adhesions: {summary['total_adhesions']}")
        print(f"   All GF(3) conserved: {summary['all_gf3_conserved']}")

    # Reload from DuckLake
    print("\n5. Reloading propagator from DuckLake...")
    with EdgePhaseDuckLake() as db:
        loaded_prop = db.load_propagator("world_demo")
        print(f"   ✅ Loaded {len(loaded_prop.bags)} bags")
        print(f"   ✅ Loaded {len(loaded_prop.adhesions)} adhesions")

        # Verify state
        satisfiable_p1, _ = loaded_prop.decide_sheaf(Phase.PHASE_1)
        print(f"   ✅ Phase 1 sheaf satisfiable: {satisfiable_p1}")


if __name__ == "__main__":
    demo()
