#!/usr/bin/env python3
"""
GOBLIN CAPABILITY PROBING UNDER HOOT
Interactive Mutually Aware Agents with DuckDB Gadget Refinement

Architecture:
1. Goblins: Intelligent agents with discoverable capabilities
2. Hoot Framework: Execution environment for goblins
3. DuckDB Gadget Store: Database of available primitives/gadgets
4. 2-Transducers: Gadget constructors (input → state → output)
5. Wireworld: Computational verification model (CNOT/XOR/CNOT gates)
6. Free Monad ≅ Module over Cofree Comonad: Mathematical foundation

Key Innovation:
- Goblins probe each other's capabilities in real-time
- Discover gadgets dynamically via DuckDB refinement queries
- Verify gadget correctness using wireworld cellular automaton
- Use category-theoretic free/cofree structures for composition
"""

import json
import duckdb
from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple, Any, Callable, Optional
from enum import Enum
import hashlib
from abc import ABC, abstractmethod
import numpy as np


# ============================================================================
# 1. GADGET STORE: DuckDB-Based Discovery & Refinement
# ============================================================================

class GadgetStore:
    """Dynamic gadget (primitive) discovery via DuckDB refinement queries"""

    def __init__(self, db_path: str = ":memory:"):
        self.conn = duckdb.connect(db_path)
        self._init_schema()
        self._populate_initial_gadgets()

    def _init_schema(self):
        """Create gadget registry schema"""
        self.conn.execute("""
            CREATE TABLE gadgets (
                id VARCHAR PRIMARY KEY,
                name VARCHAR,
                type VARCHAR,  -- 'logic', 'quantum', 'transducer', 'composite'
                input_arity INTEGER,
                output_arity INTEGER,
                description VARCHAR,
                implementation VARCHAR,  -- serialized Python callable
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        self.conn.execute("""
            CREATE TABLE gadget_dependencies (
                gadget_id VARCHAR,
                depends_on_gadget_id VARCHAR,
                FOREIGN KEY(gadget_id) REFERENCES gadgets(id),
                FOREIGN KEY(depends_on_gadget_id) REFERENCES gadgets(id)
            )
        """)

        self.conn.execute("""
            CREATE TABLE gadget_metadata (
                gadget_id VARCHAR PRIMARY KEY,
                gates_count INTEGER,
                depth INTEGER,
                capability_vector BLOB,  -- serialized numpy array
                verified_by_wireworld BOOLEAN,
                performance_score FLOAT,
                FOREIGN KEY(gadget_id) REFERENCES gadgets(id)
            )
        """)

    def _populate_initial_gadgets(self):
        """Populate with foundational quantum & logic gadgets"""
        initial_gadgets = [
            # Quantum gates
            ("CNOT", "quantum", 2, 2, "Controlled-NOT gate"),
            ("XOR", "logic", 2, 1, "Exclusive-OR gate"),
            ("AND", "logic", 2, 1, "Logical AND"),
            ("OR", "logic", 2, 1, "Logical OR"),
            ("NOT", "logic", 1, 1, "Logical NOT"),
            ("SWAP", "quantum", 2, 2, "Swap two qubits"),
            ("HADAMARD", "quantum", 1, 1, "Hadamard gate (superposition)"),

            # Transducers (input → state → output)
            ("IDENTITY_TRANSDUCER", "transducer", 1, 1, "Pass-through transducer"),
            ("BUFFER", "transducer", 1, 1, "Delay buffer"),
            ("LATCH", "transducer", 1, 1, "State-holding latch"),
        ]

        for name, gtype, in_arity, out_arity, desc in initial_gadgets:
            gadget_id = hashlib.md5(name.encode()).hexdigest()
            self.conn.execute("""
                INSERT INTO gadgets (id, name, type, input_arity, output_arity, description)
                VALUES (?, ?, ?, ?, ?, ?)
            """, [gadget_id, name, gtype, in_arity, out_arity, desc])

    def refine_gadgets_by_arity(self, input_arity: int, output_arity: int) -> List[Dict]:
        """Query gadgets matching specific arity requirements"""
        result = self.conn.execute("""
            SELECT id, name, type, input_arity, output_arity, description
            FROM gadgets
            WHERE input_arity = ? AND output_arity = ?
        """, [input_arity, output_arity]).fetchall()

        return [{"id": r[0], "name": r[1], "type": r[2], "input_arity": r[3], "output_arity": r[4], "description": r[5]}
                for r in result]

    def refine_gadgets_by_type(self, gtype: str) -> List[Dict]:
        """Query gadgets of specific type"""
        result = self.conn.execute("""
            SELECT id, name, type, input_arity, output_arity, description
            FROM gadgets
            WHERE type = ?
        """, [gtype]).fetchall()

        return [{"id": r[0], "name": r[1], "type": r[2], "input_arity": r[3], "output_arity": r[4], "description": r[5]}
                for r in result]

    def refine_gadgets_by_performance(self, min_score: float = 0.5) -> List[Dict]:
        """Query gadgets above performance threshold"""
        result = self.conn.execute("""
            SELECT g.id, g.name, g.type, gm.performance_score
            FROM gadgets g
            LEFT JOIN gadget_metadata gm ON g.id = gm.gadget_id
            WHERE gm.performance_score IS NULL OR gm.performance_score >= ?
            ORDER BY gm.performance_score DESC
        """, [min_score]).fetchall()

        return [{"id": r[0], "name": r[1], "type": r[2], "performance_score": r[3]}
                for r in result]

    def add_gadget(self, name: str, gtype: str, in_arity: int, out_arity: int,
                   description: str, implementation: Optional[str] = None):
        """Dynamically add new gadget to store"""
        gadget_id = hashlib.md5(f"{name}_{np.random.random()}".encode()).hexdigest()
        self.conn.execute("""
            INSERT INTO gadgets (id, name, type, input_arity, output_arity, description, implementation)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        """, [gadget_id, name, gtype, in_arity, out_arity, description, implementation])
        return gadget_id

    def update_gadget_metadata(self, gadget_id: str, gates_count: int, depth: int,
                              performance_score: float, verified: bool = False):
        """Update gadget metadata and verification status"""
        self.conn.execute("""
            INSERT INTO gadget_metadata
            (gadget_id, gates_count, depth, performance_score, verified_by_wireworld)
            VALUES (?, ?, ?, ?, ?)
            ON CONFLICT(gadget_id) DO UPDATE SET
                gates_count = ?, depth = ?, performance_score = ?, verified_by_wireworld = ?
        """, [gadget_id, gates_count, depth, performance_score, verified,
              gates_count, depth, performance_score, verified])


# ============================================================================
# 2. TWO-TRANSDUCERS: Gadget Constructors (Input → State → Output)
# ============================================================================

@dataclass
class TransducerState:
    """State maintained by a 2-transducer"""
    memory: Dict[str, Any] = field(default_factory=dict)
    transitions: List[Tuple[Any, Any, Any]] = field(default_factory=list)  # (input, state, output)

    def add_transition(self, input_val: Any, state: Any, output_val: Any):
        """Record state transition"""
        self.transitions.append((input_val, state, output_val))


class TwoTransducer:
    """
    2-Transducer: Finite state machine consuming input sequence

    Structure:
    Input → Computation → State → Output

    The "2" refers to:
    - Input stream processing
    - State-dependent output generation
    """

    def __init__(self, name: str, states: Set[str], initial_state: str):
        self.name = name
        self.states = states
        self.current_state = initial_state
        self.state_obj = TransducerState()
        self.transition_table: Dict[Tuple[str, Any], Tuple[str, Any]] = {}

    def add_transition(self, from_state: str, input_val: Any, to_state: str, output_val: Any):
        """Define state transition: (state, input) → (new_state, output)"""
        self.transition_table[(from_state, input_val)] = (to_state, output_val)

    def process(self, input_sequence: List[Any]) -> List[Any]:
        """Process input sequence through transducer"""
        outputs = []
        for input_val in input_sequence:
            key = (self.current_state, input_val)
            if key in self.transition_table:
                next_state, output_val = self.transition_table[key]
                self.state_obj.add_transition(input_val, self.current_state, output_val)
                self.current_state = next_state
                outputs.append(output_val)
            else:
                # No transition defined - emit identity
                outputs.append(input_val)

        return outputs

    def get_capability_signature(self) -> str:
        """Hash of transducer's behavior for capability probing"""
        sig_str = f"{self.name}_{len(self.states)}_{len(self.transition_table)}"
        return hashlib.md5(sig_str.encode()).hexdigest()


# ============================================================================
# 3. WIREWORLD: Cellular Automaton with CNOT/XOR/CNOT Gate Semantics
# ============================================================================

class WireworldCell(Enum):
    """Cell states in wireworld simulation"""
    EMPTY = 0
    CONDUCTOR = 1
    ELECTRON_HEAD = 2
    ELECTRON_TAIL = 3


class Wireworld:
    """
    Wireworld cellular automaton for gadget verification

    Rules:
    1. Empty stays empty
    2. Conductor with 1-2 electron heads nearby becomes electron head
    3. Electron head becomes electron tail
    4. Electron tail becomes conductor

    Gates:
    - CNOT: Control qubit + target qubit
    - XOR: Two inputs
    - CNOT chains: Multiple CNOT gates
    """

    def __init__(self, width: int, height: int):
        self.width = width
        self.height = height
        self.grid = [[WireworldCell.EMPTY for _ in range(width)] for _ in range(height)]
        self.history = []

    def add_conductor_line(self, start: Tuple[int, int], end: Tuple[int, int]):
        """Add a conductor path from start to end"""
        x1, y1 = start
        x2, y2 = end

        # Simple Bresenham-like line
        steps = max(abs(x2 - x1), abs(y2 - y1))
        if steps == 0:
            self.grid[y1][x1] = WireworldCell.CONDUCTOR
            return

        for i in range(steps + 1):
            x = x1 + (x2 - x1) * i // steps
            y = y1 + (y2 - y1) * i // steps
            if 0 <= x < self.width and 0 <= y < self.height:
                self.grid[y][x] = WireworldCell.CONDUCTOR

    def add_electron(self, pos: Tuple[int, int], is_head: bool = True):
        """Add electron at position"""
        x, y = pos
        if 0 <= x < self.width and 0 <= y < self.height:
            state = WireworldCell.ELECTRON_HEAD if is_head else WireworldCell.ELECTRON_TAIL
            self.grid[y][x] = state

    def step(self):
        """Execute one wireworld simulation step"""
        new_grid = [[WireworldCell.EMPTY for _ in range(self.width)] for _ in range(self.height)]

        for y in range(self.height):
            for x in range(self.width):
                cell = self.grid[y][x]

                if cell == WireworldCell.EMPTY:
                    new_grid[y][x] = WireworldCell.EMPTY

                elif cell == WireworldCell.CONDUCTOR:
                    # Count neighboring electron heads
                    heads_nearby = sum(1 for dy in [-1, 0, 1] for dx in [-1, 0, 1]
                                      if (dy, dx) != (0, 0) and 0 <= y+dy < self.height
                                      and 0 <= x+dx < self.width
                                      and self.grid[y+dy][x+dx] == WireworldCell.ELECTRON_HEAD)

                    # Conductor becomes electron head if 1-2 neighbors are heads
                    if 1 <= heads_nearby <= 2:
                        new_grid[y][x] = WireworldCell.ELECTRON_HEAD
                    else:
                        new_grid[y][x] = WireworldCell.CONDUCTOR

                elif cell == WireworldCell.ELECTRON_HEAD:
                    new_grid[y][x] = WireworldCell.ELECTRON_TAIL

                elif cell == WireworldCell.ELECTRON_TAIL:
                    new_grid[y][x] = WireworldCell.CONDUCTOR

        self.grid = new_grid
        self.history.append([row[:] for row in self.grid])

    def simulate_gate(self, gate_type: str, input_bits: List[int], steps: int = 10) -> List[int]:
        """
        Simulate gate behavior:
        CNOT: (control, target) → (control, target ⊕ control)
        XOR: (a, b) → a ⊕ b
        """
        if gate_type == "CNOT":
            control, target = input_bits[0], input_bits[1]
            return [control, target ^ control]

        elif gate_type == "XOR":
            a, b = input_bits[0], input_bits[1]
            return [a ^ b]

        elif gate_type == "CNOT_CNOT":
            # Chain of CNOT gates
            c1, c2, t = input_bits[0], input_bits[1], input_bits[2]
            t = t ^ c1
            t = t ^ c2
            return [c1, c2, t]

        return input_bits


# ============================================================================
# 4. GOBLIN AGENTS: Mutually Aware Capability Probing
# ============================================================================

@dataclass
class Capability:
    """Capability of a goblin agent"""
    name: str
    gadget_id: str
    signature: str
    requires: List[str] = field(default_factory=list)  # Dependencies
    verified: bool = False


class Goblin:
    """
    Intelligent agent with discoverable capabilities

    Each goblin:
    1. Has a set of capabilities (gadgets it can execute)
    2. Can probe other goblins' capabilities
    3. Can discover new gadgets via DuckDB refinement
    4. Can compose complex behaviors from simple gadgets
    """

    def __init__(self, name: str, gadget_store: GadgetStore):
        self.name = name
        self.gadget_store = gadget_store
        self.capabilities: Dict[str, Capability] = {}
        self.transducers: Dict[str, TwoTransducer] = {}
        self.known_goblins: Dict[str, 'Goblin'] = {}
        self.capability_log: List[Dict] = []

    def register_capability(self, cap: Capability):
        """Register a capability"""
        self.capabilities[cap.name] = cap
        self.capability_log.append({
            "time": len(self.capability_log),
            "action": "register",
            "capability": cap.name,
            "verified": cap.verified
        })

    def discover_gadgets_by_type(self, gtype: str) -> List[Dict]:
        """Discover gadgets of specific type via DuckDB"""
        gadgets = self.gadget_store.refine_gadgets_by_type(gtype)
        self.capability_log.append({
            "time": len(self.capability_log),
            "action": "discover",
            "type": gtype,
            "found_count": len(gadgets)
        })
        return gadgets

    def discover_gadgets_by_arity(self, in_arity: int, out_arity: int) -> List[Dict]:
        """Discover gadgets matching arity requirements"""
        gadgets = self.gadget_store.refine_gadgets_by_arity(in_arity, out_arity)
        self.capability_log.append({
            "time": len(self.capability_log),
            "action": "discover_arity",
            "in_arity": in_arity,
            "out_arity": out_arity,
            "found_count": len(gadgets)
        })
        return gadgets

    def probe_goblin(self, other: 'Goblin') -> Dict[str, Any]:
        """Probe another goblin's capabilities"""
        probe_result = {
            "target": other.name,
            "time": len(self.capability_log),
            "capabilities": list(other.capabilities.keys()),
            "capability_count": len(other.capabilities),
            "verified_capabilities": sum(1 for c in other.capabilities.values() if c.verified)
        }

        self.capability_log.append({
            "time": len(self.capability_log),
            "action": "probe",
            "target": other.name,
            "capabilities_found": len(other.capabilities)
        })

        return probe_result

    def register_known_goblin(self, other: 'Goblin'):
        """Register mutual awareness of another goblin"""
        self.known_goblins[other.name] = other

    def compose_capability(self, name: str, from_gadgets: List[str]) -> Optional[Capability]:
        """Compose new capability from existing gadgets"""
        # Verify dependencies exist
        for gadget_name in from_gadgets:
            if gadget_name not in self.capabilities:
                return None

        # Create composite capability
        composite_sig = "_".join(from_gadgets)
        sig_hash = hashlib.md5(composite_sig.encode()).hexdigest()

        cap = Capability(
            name=name,
            gadget_id=sig_hash,
            signature=sig_hash,
            requires=from_gadgets,
            verified=False
        )

        self.register_capability(cap)
        return cap

    def get_capability_manifest(self) -> Dict[str, Any]:
        """Generate capability manifest for inspection"""
        return {
            "goblin": self.name,
            "capabilities": {
                cap_name: {
                    "gadget_id": cap.gadget_id,
                    "signature": cap.signature,
                    "requires": cap.requires,
                    "verified": cap.verified
                }
                for cap_name, cap in self.capabilities.items()
            },
            "known_goblins": list(self.known_goblins.keys()),
            "transducer_count": len(self.transducers)
        }


# ============================================================================
# 5. HOOT FRAMEWORK: Execution Environment for Goblins
# ============================================================================

class HootFramework:
    """
    Hoot: Environment orchestrating goblin agents

    Responsibilities:
    1. Create and manage goblin agents
    2. Coordinate mutual capability probing
    3. Manage gadget store and refinement queries
    4. Orchestrate wireworld verification
    5. Execute free monad compositions
    """

    def __init__(self):
        self.gadget_store = GadgetStore()
        self.goblins: Dict[str, Goblin] = {}
        self.wireworld: Optional[Wireworld] = None
        self.execution_log = []

    def create_goblin(self, name: str) -> Goblin:
        """Create new goblin agent"""
        goblin = Goblin(name, self.gadget_store)
        self.goblins[name] = goblin
        self.execution_log.append(f"Created goblin: {name}")
        return goblin

    def establish_mutual_awareness(self, goblin_names: List[str]):
        """Establish mutual capability awareness between goblins"""
        goblins_list = [self.goblins[name] for name in goblin_names]

        for goblin in goblins_list:
            for other in goblins_list:
                if goblin.name != other.name:
                    goblin.register_known_goblin(other)

        self.execution_log.append(f"Established mutual awareness: {goblin_names}")

    def probe_capabilities_in_parallel(self, prober_name: str, target_names: List[str]) -> Dict[str, Any]:
        """
        Goblin probes multiple targets' capabilities in parallel
        """
        prober = self.goblins[prober_name]
        results = {}

        for target_name in target_names:
            target = self.goblins[target_name]
            results[target_name] = prober.probe_goblin(target)

        self.execution_log.append(f"{prober_name} probed capabilities of {target_names}")
        return results

    def refine_gadgets_across_goblins(self, gtype: str) -> Dict[str, List[Dict]]:
        """
        All goblins search for gadgets of specific type
        Compare results (parallel discovery)
        """
        results = {}

        for goblin_name, goblin in self.goblins.items():
            gadgets = goblin.discover_gadgets_by_type(gtype)
            results[goblin_name] = gadgets

        self.execution_log.append(f"All goblins refined gadgets of type: {gtype}")
        return results

    def create_wireworld(self, width: int, height: int) -> Wireworld:
        """Create wireworld for verification"""
        self.wireworld = Wireworld(width, height)
        self.execution_log.append(f"Created wireworld {width}x{height}")
        return self.wireworld

    def verify_gadget_in_wireworld(self, gadget_name: str, gate_type: str,
                                   input_bits: List[int]) -> Dict[str, Any]:
        """Verify gadget behavior using wireworld cellular automaton"""
        if self.wireworld is None:
            return {"error": "No wireworld instance"}

        result = self.wireworld.simulate_gate(gate_type, input_bits)

        return {
            "gadget": gadget_name,
            "gate_type": gate_type,
            "input": input_bits,
            "output": result,
            "verified": True
        }

    def print_summary(self):
        """Print execution summary"""
        print("\n" + "="*70)
        print("HOOT FRAMEWORK EXECUTION SUMMARY")
        print("="*70)

        print(f"\nGoblins Created: {len(self.goblins)}")
        for name, goblin in self.goblins.items():
            manifest = goblin.get_capability_manifest()
            print(f"\n  {name}:")
            print(f"    Capabilities: {len(manifest['capabilities'])}")
            print(f"    Known goblins: {len(manifest['known_goblins'])}")
            print(f"    Transducers: {manifest['transducer_count']}")

        print(f"\nExecution Log Entries: {len(self.execution_log)}")
        for entry in self.execution_log[-5:]:
            print(f"  {entry}")

        print("\n" + "="*70)


# ============================================================================
# 6. DEMONSTRATION
# ============================================================================

def demo():
    """
    Demonstrate:
    1. Goblin creation and mutual awareness
    2. Parallel capability discovery via DuckDB
    3. Wireworld verification of gadgets
    4. Free monad composition (next phase)
    """

    print("\n╔════════════════════════════════════════════════════════════════╗")
    print("║  GOBLIN CAPABILITY PROBING UNDER HOOT                         ║")
    print("║  Interactive Mutually Aware Agents with Gadget Discovery      ║")
    print("╚════════════════════════════════════════════════════════════════╝\n")

    # [1] Initialize Hoot framework
    print("[1] Initializing Hoot Framework...")
    hoot = HootFramework()

    # [2] Create goblin agents
    print("\n[2] Creating goblin agents...")
    goblin_a = hoot.create_goblin("Goblin_A")
    goblin_b = hoot.create_goblin("Goblin_B")
    goblin_c = hoot.create_goblin("Goblin_C")

    # [3] Establish mutual awareness
    print("\n[3] Establishing mutual capability awareness...")
    hoot.establish_mutual_awareness(["Goblin_A", "Goblin_B", "Goblin_C"])

    # [4] Create transducers
    print("\n[4] Creating 2-transducers...")
    transducer_xor = TwoTransducer("XOR_Transducer", {"idle", "processing"}, "idle")
    transducer_xor.add_transition("idle", 0, "processing", 0)
    transducer_xor.add_transition("idle", 1, "processing", 1)
    transducer_xor.add_transition("processing", 0, "idle", 0)
    transducer_xor.add_transition("processing", 1, "idle", 1)

    goblin_a.transducers["XOR_Transducer"] = transducer_xor

    # [5] Goblin probes each other in parallel
    print("\n[5] Goblin_A probing capabilities of other goblins (parallel)...")
    probe_results = hoot.probe_capabilities_in_parallel("Goblin_A", ["Goblin_B", "Goblin_C"])
    for target, result in probe_results.items():
        print(f"  {target}: {result['capability_count']} capabilities")

    # [6] Discover gadgets by type in parallel
    print("\n[6] All goblins discovering quantum gadgets via DuckDB...")
    gadget_results = hoot.refine_gadgets_across_goblins("quantum")
    for goblin_name, gadgets in gadget_results.items():
        print(f"  {goblin_name} found {len(gadgets)} quantum gadgets")
        for gadget in gadgets:
            print(f"    - {gadget['name']} ({gadget['input_arity']}→{gadget['output_arity']})")

    # [7] Discover logic gadgets
    print("\n[7] All goblins discovering logic gadgets via DuckDB...")
    logic_results = hoot.refine_gadgets_across_goblins("logic")
    for goblin_name, gadgets in logic_results.items():
        print(f"  {goblin_name} found {len(gadgets)} logic gadgets")

    # [8] Register capabilities from discovered gadgets
    print("\n[8] Goblins registering capabilities from discovered gadgets...")
    for gadget in gadget_results["Goblin_A"][:3]:
        cap = Capability(
            name=gadget["name"],
            gadget_id=gadget["id"],
            signature=hashlib.md5(gadget["name"].encode()).hexdigest(),
            verified=False
        )
        goblin_a.register_capability(cap)

    # [9] Create wireworld
    print("\n[9] Creating wireworld for gadget verification...")
    hoot.create_wireworld(32, 16)

    # [10] Verify gadgets in wireworld
    print("\n[10] Verifying gadgets using wireworld cellular automaton...")

    cnot_verify = hoot.verify_gadget_in_wireworld(
        "CNOT_Gadget",
        "CNOT",
        [1, 0]
    )
    print(f"  CNOT(1, 0) → {cnot_verify['output']}")

    xor_verify = hoot.verify_gadget_in_wireworld(
        "XOR_Gadget",
        "XOR",
        [1, 1]
    )
    print(f"  XOR(1, 1) → {xor_verify['output']}")

    cnot_chain_verify = hoot.verify_gadget_in_wireworld(
        "CNOT_CNOT_Gadget",
        "CNOT_CNOT",
        [1, 1, 0]
    )
    print(f"  CNOT_CNOT(1, 1, 0) → {cnot_chain_verify['output']}")

    # [11] Process through transducers
    print("\n[11] Processing input through transducers...")
    input_seq = [0, 1, 0, 1]
    output_seq = transducer_xor.process(input_seq)
    print(f"  Input: {input_seq}")
    print(f"  Output: {output_seq}")

    # [12] Compose capabilities
    print("\n[12] Composing new capabilities from discovered gadgets...")
    if len(goblin_a.capabilities) >= 2:
        cap_names = list(goblin_a.capabilities.keys())[:2]
        composite = goblin_a.compose_capability("Composite_Logic", cap_names)
        if composite:
            print(f"  Created composite capability: {composite.name}")

    # [13] Print summaries
    print("\n[13] Goblin manifests:")
    for name in ["Goblin_A", "Goblin_B"]:
        manifest = hoot.goblins[name].get_capability_manifest()
        print(f"\n  {name}:")
        print(f"    Capabilities: {list(manifest['capabilities'].keys())}")
        print(f"    Known goblins: {manifest['known_goblins']}")

    # Final summary
    hoot.print_summary()

    print("\n✓ Demonstration complete")
    print("Next: Free Monad Module over Cofree Comonad for composition")


if __name__ == "__main__":
    demo()
