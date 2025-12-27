#!/usr/bin/env python3
"""
Libkind-Spivak Dynamical Systems Operads

Based on:
- Sophie Libkind's thesis "Composition and Computation in Dynamical Systems" (Stanford 2023)
- "Operadic Modeling of Dynamical Systems" (ACT 2021)
- AlgebraicDynamics.jl

Operads for compositional dynamical systems:
1. Directed Composition (⊳): Output → Input wiring
2. Undirected Composition (○): Interface matching via pullback
3. Machines Operad: State machines with internal dynamics
4. Open Dynamical Systems: dx/dt = f(x, u), y = g(x)
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import IntEnum
from typing import Any, Callable, TypeVar

# ═══════════════════════════════════════════════════════════════════════════════
# GF(3) TRIT ASSIGNMENTS
# ═══════════════════════════════════════════════════════════════════════════════

class Trit(IntEnum):
    MINUS = -1    # Undirected (structure-preserving)
    ERGODIC = 0   # Interface (neutral boundary)
    PLUS = 1      # Directed (forward dynamics)


# ═══════════════════════════════════════════════════════════════════════════════
# INTERFACES: Typed Ports
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Port:
    """A typed port for wiring."""
    name: str
    port_type: str  # Type label
    direction: str  # "in", "out", or "inout"
    
    def compatible(self, other: Port) -> bool:
        """Check if ports can be wired together."""
        return (self.port_type == other.port_type and
                ((self.direction == "out" and other.direction == "in") or
                 (self.direction == "inout")))


@dataclass
class Interface:
    """Interface = collection of typed ports."""
    inputs: list[Port] = field(default_factory=list)
    outputs: list[Port] = field(default_factory=list)
    
    @property
    def all_ports(self) -> list[Port]:
        return self.inputs + self.outputs
    
    def __add__(self, other: Interface) -> Interface:
        """Monoidal product of interfaces."""
        return Interface(
            inputs=self.inputs + other.inputs,
            outputs=self.outputs + other.outputs,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# DIRECTED COMPOSITION OPERAD (⊳)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class DirectedBox:
    """
    A box in a directed wiring diagram.
    
    Morphism in Mach category:
        inputs → [internal dynamics] → outputs
    """
    name: str
    interface: Interface
    dynamics: Callable[[Any, Any], Any] = None  # f(state, input) → (new_state, output)
    state: Any = None
    trit: int = Trit.PLUS
    
    def __call__(self, inputs: dict) -> dict:
        """Execute the box dynamics."""
        if self.dynamics is None:
            return {p.name: inputs.get(p.name) for p in self.interface.outputs}
        new_state, outputs = self.dynamics(self.state, inputs)
        self.state = new_state
        return outputs


class DirectedCompositionOperad:
    """
    Operad for directed wiring diagrams.
    
    Composition (⊳): Connect output ports to input ports.
    Trit: +1 (PLUS, forward dynamics)
    
    From Libkind thesis:
        "Directed wiring diagrams model systems where information flows
         in a specified direction, from outputs to inputs."
    """
    
    trit = Trit.PLUS
    
    def __init__(self):
        self.boxes: list[DirectedBox] = []
        self.wires: list[tuple[str, str, str, str]] = []  # (src_box, src_port, tgt_box, tgt_port)
    
    def add_box(self, box: DirectedBox):
        """Add a box to the diagram."""
        self.boxes.append(box)
    
    def wire(self, src_box: str, src_port: str, tgt_box: str, tgt_port: str):
        """Connect output of src to input of tgt."""
        self.wires.append((src_box, src_port, tgt_box, tgt_port))
    
    def compose(self, inner: DirectedCompositionOperad, at_port: str) -> DirectedCompositionOperad:
        """
        Operadic composition: Insert inner diagram at port.
        
        (outer ⊳_port inner): Replace port with inner's interface
        """
        result = DirectedCompositionOperad()
        result.boxes = self.boxes + inner.boxes
        result.wires = self.wires + inner.wires
        # Rewire the connection point
        # (Full implementation would handle port matching)
        return result
    
    def evaluate(self, inputs: dict) -> dict:
        """Execute the composed system."""
        values = inputs.copy()
        
        # Topological sort of boxes by wires
        for box in self.boxes:
            box_inputs = {}
            for wire in self.wires:
                if wire[2] == box.name:
                    box_inputs[wire[3]] = values.get(f"{wire[0]}.{wire[1]}")
            
            outputs = box(box_inputs)
            for port_name, value in outputs.items():
                values[f"{box.name}.{port_name}"] = value
        
        return values


# ═══════════════════════════════════════════════════════════════════════════════
# UNDIRECTED COMPOSITION OPERAD (○)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class UndirectedBox:
    """
    A box in an undirected wiring diagram.
    
    No distinction between inputs and outputs - just "exposed wires".
    Composition happens by matching wires (interface pullback).
    """
    name: str
    exposed_wires: list[Port]  # Wires going to boundary
    internal_wires: list[Port] = field(default_factory=list)
    relation: Callable[[dict], bool] = None  # Constraint relation
    trit: int = Trit.MINUS


class UndirectedCompositionOperad:
    """
    Operad for undirected wiring diagrams.
    
    Composition (○): Match exposed wires by pullback.
    Trit: -1 (MINUS, structure-preserving)
    
    From Libkind thesis:
        "Undirected composition corresponds to pullback in the
         category of typed finite sets."
    """
    
    trit = Trit.MINUS
    
    def __init__(self):
        self.boxes: list[UndirectedBox] = []
        self.junctions: list[set[str]] = []  # Sets of wire names that are joined
    
    def add_box(self, box: UndirectedBox):
        self.boxes.append(box)
    
    def join(self, *wire_names: str):
        """Join wires at a junction (undirected connection)."""
        self.junctions.append(set(wire_names))
    
    def compose(self, inner: UndirectedCompositionOperad, matching: dict[str, str]) -> UndirectedCompositionOperad:
        """
        Operadic composition via pullback.
        
        matching: {inner_wire: outer_wire} - which wires to identify
        """
        result = UndirectedCompositionOperad()
        result.boxes = self.boxes + inner.boxes
        result.junctions = self.junctions + inner.junctions
        
        # Add junctions for matched wires
        for inner_wire, outer_wire in matching.items():
            result.junctions.append({inner_wire, outer_wire})
        
        return result
    
    def exposed_interface(self) -> list[Port]:
        """Get the external interface (wires not internal)."""
        all_wires = []
        for box in self.boxes:
            all_wires.extend(box.exposed_wires)
        
        # Remove wires that are internal (joined to other internal wires)
        internal = set()
        for junction in self.junctions:
            if len(junction) > 1:
                internal.update(junction)
        
        return [w for w in all_wires if w.name not in internal]


# ═══════════════════════════════════════════════════════════════════════════════
# MACHINES OPERAD
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Machine:
    """
    A machine with internal state.
    
    Morphism in Mach_state category:
        (state, input) → (state', output)
    """
    name: str
    state_type: str
    interface: Interface
    transition: Callable[[Any, dict], tuple[Any, dict]]  # (s, u) → (s', y)
    initial_state: Any = None
    trit: int = Trit.ERGODIC


class MachinesOperad:
    """
    Operad of machines (stateful systems).
    
    Trit: 0 (ERGODIC, neutral interface)
    
    From Libkind thesis:
        "Machines are morphisms in the category Mach where
         composition corresponds to wiring diagrams."
    """
    
    trit = Trit.ERGODIC
    
    def __init__(self):
        self.machines: list[Machine] = []
        self.directed = DirectedCompositionOperad()
    
    def add_machine(self, machine: Machine):
        self.machines.append(machine)
        self.directed.add_box(DirectedBox(
            name=machine.name,
            interface=machine.interface,
            dynamics=machine.transition,
            state=machine.initial_state,
        ))
    
    def wire(self, src: str, src_port: str, tgt: str, tgt_port: str):
        self.directed.wire(src, src_port, tgt, tgt_port)
    
    def step(self, inputs: dict) -> dict:
        """Execute one step of the composed machine."""
        return self.directed.evaluate(inputs)


# ═══════════════════════════════════════════════════════════════════════════════
# OPEN DYNAMICAL SYSTEMS OPERAD
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class OpenDynamicalSystem:
    """
    Open dynamical system: dx/dt = f(x, u), y = g(x)
    
    Where:
        x ∈ X (state space)
        u ∈ U (input space)
        y ∈ Y (output space)
        f: X × U → TX (dynamics)
        g: X → Y (readout)
    """
    name: str
    state_dim: int
    input_dim: int
    output_dim: int
    dynamics: Callable[[list, list], list]  # f(x, u) → dx/dt
    readout: Callable[[list], list]  # g(x) → y
    state: list = field(default_factory=list)
    trit: int = Trit.PLUS
    
    def step(self, dt: float, inputs: list) -> list:
        """Euler integration step."""
        dxdt = self.dynamics(self.state, inputs)
        self.state = [x + dt * dx for x, dx in zip(self.state, dxdt)]
        return self.readout(self.state)


class DynamicalSystemsOperad:
    """
    Operad of open dynamical systems.
    
    Trit: +1 (PLUS, forward dynamics)
    
    From AlgebraicDynamics.jl:
        "Compose ODEs by wiring outputs to inputs."
    """
    
    trit = Trit.PLUS
    
    def __init__(self):
        self.systems: list[OpenDynamicalSystem] = []
        self.couplings: list[tuple[str, int, str, int]] = []  # (src, out_idx, tgt, in_idx)
    
    def add_system(self, system: OpenDynamicalSystem):
        self.systems.append(system)
    
    def couple(self, src: str, out_idx: int, tgt: str, in_idx: int):
        """Couple output of src system to input of tgt system."""
        self.couplings.append((src, out_idx, tgt, in_idx))
    
    def simulate(self, dt: float, n_steps: int, external_inputs: dict[str, list]) -> dict[str, list[list]]:
        """Simulate the composed system."""
        trajectories = {s.name: [] for s in self.systems}
        
        for _ in range(n_steps):
            outputs = {}
            
            # Compute outputs
            for system in self.systems:
                ext_input = external_inputs.get(system.name, [0.0] * system.input_dim)
                
                # Add coupled inputs
                coupled_input = list(ext_input)
                for src, out_idx, tgt, in_idx in self.couplings:
                    if tgt == system.name:
                        src_output = outputs.get(src, [0.0] * len(ext_input))
                        if in_idx < len(coupled_input) and out_idx < len(src_output):
                            coupled_input[in_idx] += src_output[out_idx]
                
                output = system.step(dt, coupled_input)
                outputs[system.name] = output
                trajectories[system.name].append(list(system.state))
        
        return trajectories


# ═══════════════════════════════════════════════════════════════════════════════
# REGISTRY
# ═══════════════════════════════════════════════════════════════════════════════

LIBKIND_SPIVAK_OPERADS = {
    "directed": DirectedCompositionOperad,
    "undirected": UndirectedCompositionOperad,
    "machines": MachinesOperad,
    "dynamical": DynamicalSystemsOperad,
}

GF3_ASSIGNMENTS = {
    "directed": Trit.PLUS,      # Forward flow
    "undirected": Trit.MINUS,   # Structure-preserving
    "machines": Trit.ERGODIC,   # Neutral interface
    "dynamical": Trit.PLUS,     # Forward dynamics
}

# Verify GF(3) conservation: +1 + (-1) + 0 + (+1) = 1... need adjustment
# Actually: directed (+1) + undirected (-1) + machines (0) + dynamical (+1) = +1
# For conservation, we'd pair with complementary operads

def verify_gf3() -> bool:
    """Verify GF(3) sum mod 3 = 0."""
    total = sum(GF3_ASSIGNMENTS.values())
    return total % 3 == 0


# ═══════════════════════════════════════════════════════════════════════════════
# DEMO
# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("═══ Libkind-Spivak Dynamical Systems Operads ═══\n")
    
    # 1. Directed composition example
    directed = DirectedCompositionOperad()
    box1 = DirectedBox(
        name="sensor",
        interface=Interface(
            inputs=[Port("signal", "Real", "in")],
            outputs=[Port("measurement", "Real", "out")],
        ),
    )
    box2 = DirectedBox(
        name="controller",
        interface=Interface(
            inputs=[Port("measurement", "Real", "in")],
            outputs=[Port("command", "Real", "out")],
        ),
    )
    directed.add_box(box1)
    directed.add_box(box2)
    directed.wire("sensor", "measurement", "controller", "measurement")
    
    print(f"Directed operad: {len(directed.boxes)} boxes, {len(directed.wires)} wires")
    print(f"  Trit: {directed.trit} (PLUS)")
    
    # 2. Dynamical systems example
    dyn = DynamicalSystemsOperad()
    
    # Harmonic oscillator: dx/dt = v, dv/dt = -kx
    oscillator = OpenDynamicalSystem(
        name="oscillator",
        state_dim=2,
        input_dim=1,
        output_dim=1,
        dynamics=lambda x, u: [x[1], -x[0] + u[0]],
        readout=lambda x: [x[0]],
        state=[1.0, 0.0],
    )
    dyn.add_system(oscillator)
    
    # Simulate
    traj = dyn.simulate(dt=0.1, n_steps=10, external_inputs={"oscillator": [0.0]})
    print(f"\nDynamical system: oscillator trajectory (10 steps)")
    print(f"  Initial: {[1.0, 0.0]}")
    print(f"  Final:   {traj['oscillator'][-1]}")
    
    # 3. GF(3) check
    print(f"\n─── GF(3) Assignments ───")
    for name, trit in GF3_ASSIGNMENTS.items():
        label = {-1: "⊖", 0: "⊙", 1: "⊕"}[trit]
        print(f"  {name:15} {label} ({trit})")
    print(f"  Total mod 3: {sum(GF3_ASSIGNMENTS.values()) % 3}")
