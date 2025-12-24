#!/usr/bin/env python3
"""
DiscoHy Thread Operad: Materialize thread trees as rooted color operads

This is the Python version of the Hy implementation, designed to work with
uv/uvx/ruff tooling.

Skill Integration: discohy-streams + acsets + glass-bead-game

The thread network becomes a colored operad where:
  - Threads are vertices (operations)
  - Continuations are edges (typed by TAP state)
  - Colors are deterministic from thread ID
  - Operad variant is dynamically selectable
"""

from __future__ import annotations

import hashlib
import json
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from datetime import datetime
from enum import IntEnum
from typing import Any

# ═══════════════════════════════════════════════════════════════════════════════
# CONSTANTS: SplitMix64 + Golden Ratio
# ═══════════════════════════════════════════════════════════════════════════════

GOLDEN: int = 0x9E3779B97F4A7C15
MIX1: int = 0xBF58476D1CE4E5B9
MIX2: int = 0x94D049BB133111EB
MASK64: int = 0xFFFFFFFFFFFFFFFF


class TAPState(IntEnum):
    """Tripartite Awareness Protocol states."""

    BACKFILL = -1  # Historical, archived
    VERIFY = 0  # Verification, neutral
    LIVE = 1  # Forward, real-time


# ═══════════════════════════════════════════════════════════════════════════════
# COLOR GENERATION: SplitMix64 Deterministic
# ═══════════════════════════════════════════════════════════════════════════════


def mix64(z: int) -> int:
    """SplitMix64 mixing function."""
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    return (z ^ (z >> 31)) & MASK64


def thread_id_to_seed(thread_id: str) -> int:
    """Convert thread ID (T-uuid) to deterministic seed."""
    return int(hashlib.sha256(thread_id.encode()).hexdigest(), 16) & MASK64


@dataclass
class LCHColor:
    """LCH color space representation."""

    L: float  # Lightness 0-100
    C: float  # Chroma 0-150
    H: float  # Hue 0-360

    def to_dict(self) -> dict[str, float]:
        return {"L": self.L, "C": self.C, "H": self.H}

    def to_trit(self) -> int:
        """Map hue to GF(3) trit."""
        if self.H < 60 or self.H >= 300:
            return TAPState.LIVE  # warm → +1
        elif self.H < 180:
            return TAPState.VERIFY  # neutral → 0
        else:
            return TAPState.BACKFILL  # cool → -1

    def to_hex(self) -> str:
        """Approximate hex color (simplified LCH→RGB)."""
        # Simplified: map hue to RGB directly
        h = self.H / 360
        if h < 1 / 3:
            r, g, b = 1 - 3 * h, 3 * h, 0
        elif h < 2 / 3:
            r, g, b = 0, 2 - 3 * h, 3 * h - 1
        else:
            r, g, b = 3 * h - 2, 0, 3 - 3 * h
        # Apply lightness
        l_factor = self.L / 100
        r, g, b = r * l_factor, g * l_factor, b * l_factor
        return f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}"


def seed_to_lch(seed: int, index: int) -> LCHColor:
    """Generate LCH color from seed at index."""
    h = mix64((seed + index * GOLDEN) & MASK64)
    return LCHColor(
        L=25 + ((h >> 48) & 0xFFFF) / 65535 * 50,  # 25-75 lightness
        C=((h >> 32) & 0xFFFF) / 65535 * 100,  # 0-100 chroma
        H=((h >> 16) & 0xFFFF) / 65535 * 360,  # 0-360 hue
    )


# ═══════════════════════════════════════════════════════════════════════════════
# OPERAD VARIANTS: Dynamically Selectable
# ═══════════════════════════════════════════════════════════════════════════════


class OperadVariant(ABC):
    """Base class for operad variants. Each variant defines composition rules."""

    def __init__(self, name: str, description: str, trit: int = 0):
        self.name = name
        self.description = description
        self.trit = trit

    @abstractmethod
    def compose(
        self, op1: dict[str, Any], op2: dict[str, Any], port: int
    ) -> dict[str, Any]:
        """Compose op1 ∘_port op2."""
        pass


class DendroidalOperad(OperadVariant):
    """Dendroidal operad: Trees as colored operads, Ω(T) construction.
    From mathpix snip 9fda228d: vertices = operations, edges = colors.
    """

    def __init__(self):
        super().__init__(
            "dendroidal", "Tree-structured operations with edge coloring", trit=0
        )

    def compose(
        self, op1: dict[str, Any], op2: dict[str, Any], port: int
    ) -> dict[str, Any]:
        """Graft op2 at leaf `port` of op1."""
        return {
            "type": "graft",
            "outer": op1,
            "inner": op2,
            "port": port,
            "result_arity": op1.get("arity", 1) + op2.get("arity", 1) - 1,
        }


class ColoredSymmetricOperad(OperadVariant):
    """Σ-colored operad with symmetric group action.
    From mathpix snip 0c9f8554: Left Kan extension to Σ-colored.
    """

    def __init__(self):
        super().__init__(
            "colored-symmetric", "Symmetric group action on colors", trit=-1
        )

    def compose(
        self, op1: dict[str, Any], op2: dict[str, Any], port: int
    ) -> dict[str, Any]:
        """Compose with permutation tracking."""
        n = op1.get("arity", 1) + op2.get("arity", 1) - 1
        return {
            "type": "symmetric-compose",
            "outer": op1,
            "inner": op2,
            "port": port,
            "permutation": list(range(n)),
        }


class ActegoryOperad(OperadVariant):
    """Actegory: Monoidal category M acting on category C.
    From mathpix snip 12a80732: Parametrised morphisms.
    """

    def __init__(self):
        super().__init__("actegory", "Monoidal action on morphisms", trit=0)

    def compose(
        self, op1: dict[str, Any], op2: dict[str, Any], port: int
    ) -> dict[str, Any]:
        """Compose with monoidal action parameter."""
        return {
            "type": "actegory-compose",
            "outer": op1,
            "inner": op2,
            "port": port,
            "action_param": {"action": "tensor"},
        }


class TwoTransducerOperad(OperadVariant):
    """2-Transducer operad: Loregian's categorical automata.
    (Q, t) : A •→ B where t : A × Q^op × Q × B* → Set
    """

    def __init__(self):
        super().__init__("2-transducer", "Categorical automata with state", trit=1)

    def compose(
        self, op1: dict[str, Any], op2: dict[str, Any], port: int
    ) -> dict[str, Any]:
        """Compose transducers via Day convolution."""
        return {
            "type": "transducer-compose",
            "outer": op1,
            "inner": op2,
            "port": port,
            "state_product": op1.get("state_dim", 1) * op2.get("state_dim", 1),
        }


# Registry of available operad variants
OPERAD_VARIANTS: dict[str, OperadVariant] = {
    "dendroidal": DendroidalOperad(),
    "colored-symmetric": ColoredSymmetricOperad(),
    "actegory": ActegoryOperad(),
    "2-transducer": TwoTransducerOperad(),
}


# ═══════════════════════════════════════════════════════════════════════════════
# THREAD OPERAD NODE: Vertex in the rooted tree
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class ThreadOperadNode:
    """A thread as an operad operation with colored inputs/outputs."""

    thread_id: str
    title: str
    seed: int = field(init=False)
    parent_id: str | None = None
    children: list[ThreadOperadNode] = field(default_factory=list)
    message_count: int = 0
    created_at: datetime | None = None

    # 3 parallel color streams (DiscoHy)
    colors: dict[str, LCHColor] = field(default_factory=dict)
    trit: int = 0
    arity: int = 0

    def __post_init__(self):
        self.seed = thread_id_to_seed(self.thread_id)
        self.colors = {
            "LIVE": seed_to_lch(self.seed, 0),
            "VERIFY": seed_to_lch(self.seed, 1),
            "BACKFILL": seed_to_lch(self.seed, 2),
        }
        self.trit = self.colors["LIVE"].to_trit()

    def add_child(self, child: ThreadOperadNode) -> None:
        """Add continuation thread as child."""
        self.children.append(child)
        child.parent_id = self.thread_id
        self.arity = len(self.children)

    def get_color(self, stream: str = "LIVE") -> LCHColor:
        """Get color for specific stream (LIVE/VERIFY/BACKFILL)."""
        return self.colors.get(stream, self.colors["LIVE"])

    def to_dict(self) -> dict[str, Any]:
        """Serialize to dictionary."""
        return {
            "thread_id": self.thread_id,
            "title": self.title,
            "seed": self.seed,
            "parent_id": self.parent_id,
            "arity": self.arity,
            "trit": self.trit,
            "colors": {k: v.to_dict() for k, v in self.colors.items()},
            "message_count": self.message_count,
            "children": [c.to_dict() for c in self.children],
        }


# ═══════════════════════════════════════════════════════════════════════════════
# ROOTED COLOR OPERAD: The full tree structure
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class RootedColorOperad:
    """A rooted tree of threads as a colored operad.

    Mathematical structure:
    - Objects: TAP states {LIVE, VERIFY, BACKFILL}
    - Morphisms: Threads as operations
    - Composition: Thread continuation (grafting)
    - Colors: Deterministic from thread ID via SplitMix64
    """

    root_id: str
    variant: OperadVariant = field(default_factory=DendroidalOperad)
    genesis_seed: int = 0x42D
    nodes: dict[str, ThreadOperadNode] = field(default_factory=dict)

    def add_thread(
        self,
        thread_id: str,
        title: str,
        parent_id: str | None = None,
        message_count: int = 0,
        created_at: datetime | None = None,
    ) -> ThreadOperadNode:
        """Add a thread to the operad."""
        node = ThreadOperadNode(
            thread_id=thread_id,
            title=title,
            parent_id=parent_id,
            message_count=message_count,
            created_at=created_at,
        )
        self.nodes[thread_id] = node

        # Link to parent if specified
        if parent_id and parent_id in self.nodes:
            self.nodes[parent_id].add_child(node)

        return node

    def compose(
        self, thread_id_1: str, thread_id_2: str, port: int
    ) -> dict[str, Any] | None:
        """Compose two threads using current operad variant."""
        op1 = self.nodes.get(thread_id_1)
        op2 = self.nodes.get(thread_id_2)
        if op1 and op2:
            return self.variant.compose(op1.to_dict(), op2.to_dict(), port)
        return None

    def set_variant(self, variant_name: str) -> bool:
        """Dynamically switch operad variant."""
        if variant_name in OPERAD_VARIANTS:
            self.variant = OPERAD_VARIANTS[variant_name]
            return True
        return False

    def get_root(self) -> ThreadOperadNode | None:
        """Get the root node."""
        return self.nodes.get(self.root_id)

    def gf3_conservation(self) -> dict[str, Any]:
        """Check GF(3) conservation across all triplets of children."""
        violations = []
        for node in self.nodes.values():
            if len(node.children) >= 3:
                for i in range(len(node.children) - 2):
                    triplet = node.children[i : i + 3]
                    trit_sum = sum(c.trit for c in triplet)
                    if trit_sum % 3 != 0:
                        violations.append(
                            {
                                "parent": node.thread_id,
                                "triplet": [c.thread_id for c in triplet],
                                "trit_sum": trit_sum,
                            }
                        )
        return {"conserved": len(violations) == 0, "violations": violations}

    def to_discopy_diagram(self) -> dict[str, Any]:
        """Convert to DisCoPy monoidal diagram representation."""
        boxes = []
        for tid, node in self.nodes.items():
            boxes.append(
                {
                    "name": tid,
                    "dom": [node.parent_id] if node.parent_id else ["ROOT"],
                    "cod": [c.thread_id for c in node.children],
                    "color": node.colors["LIVE"].to_dict(),
                }
            )

        wires = []
        for tid, node in self.nodes.items():
            for c in node.children:
                wires.append(
                    {
                        "src": tid,
                        "tgt": c.thread_id,
                        "color": c.colors["VERIFY"].to_dict(),
                    }
                )

        return {"type": "monoidal_diagram", "boxes": boxes, "wires": wires}

    def to_dict(self) -> dict[str, Any]:
        """Serialize entire operad."""
        return {
            "root_id": self.root_id,
            "variant": self.variant.name,
            "genesis_seed": self.genesis_seed,
            "node_count": len(self.nodes),
            "gf3_check": self.gf3_conservation(),
            "nodes": {k: v.to_dict() for k, v in self.nodes.items()},
        }


# ═══════════════════════════════════════════════════════════════════════════════
# MERMAID DIAGRAM GENERATION
# ═══════════════════════════════════════════════════════════════════════════════


def operad_to_mermaid(operad: RootedColorOperad, color_stream: str = "LIVE") -> str:
    """Generate Mermaid flowchart for thread operad."""
    lines = ["flowchart TD"]

    # Style definitions based on trit
    lines.append("    classDef plus fill:#D82626,stroke:#fff,color:#fff")
    lines.append("    classDef ergodic fill:#26D826,stroke:#fff,color:#fff")
    lines.append("    classDef minus fill:#2626D8,stroke:#fff,color:#fff")

    # Add nodes
    for tid, node in operad.nodes.items():
        short_id = tid[:12]
        label = node.title.replace('"', "'")
        label = label[:27] + "..." if len(label) > 30 else label
        lines.append(f'    {short_id}["{label}"]')

    # Add edges
    for tid, node in operad.nodes.items():
        short_id = tid[:12]
        for child in node.children:
            child_short = child.thread_id[:12]
            if child.trit == TAPState.LIVE:
                edge_label = "LIVE"
            elif child.trit == TAPState.VERIFY:
                edge_label = "VERIFY"
            else:
                edge_label = "BACKFILL"
            lines.append(f"    {short_id} -->|{edge_label}| {child_short}")

    # Apply classes based on trit
    for tid, node in operad.nodes.items():
        short_id = tid[:12]
        if node.trit == TAPState.LIVE:
            class_name = "plus"
        elif node.trit == TAPState.VERIFY:
            class_name = "ergodic"
        else:
            class_name = "minus"
        lines.append(f"    class {short_id} {class_name}")

    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# THREAD TREE BUILDER
# ═══════════════════════════════════════════════════════════════════════════════


def build_operad_from_threads(
    threads: list[dict[str, Any]],
    variant: str = "dendroidal",
    seed: int = 0x42D,
) -> RootedColorOperad | None:
    """Build a RootedColorOperad from a list of thread dicts."""
    if not threads:
        return None

    # Sort by creation time
    sorted_threads = sorted(threads, key=lambda t: t.get("created", 0))

    # First thread is root
    root_thread = sorted_threads[0]
    operad = RootedColorOperad(
        root_id=root_thread["id"],
        variant=OPERAD_VARIANTS.get(variant, DendroidalOperad()),
        genesis_seed=seed,
    )

    # Add root
    operad.add_thread(
        root_thread["id"],
        root_thread.get("title", "Untitled"),
        message_count=root_thread.get("messageCount", 0),
    )

    # Add remaining threads
    prev_id = root_thread["id"]
    for thread in sorted_threads[1:]:
        tid = thread["id"]
        operad.add_thread(
            tid,
            thread.get("title", "Untitled"),
            parent_id=prev_id,
            message_count=thread.get("messageCount", 0),
        )
        prev_id = tid

    return operad


# ═══════════════════════════════════════════════════════════════════════════════
# CLI / MAIN
# ═══════════════════════════════════════════════════════════════════════════════


def main():
    """Demo the DiscoHy Thread Operad."""
    try:
        from rich.console import Console
        from rich.table import Table

        console = Console()
        use_rich = True
    except ImportError:
        console = None
        use_rich = False

    print("═══ DiscoHy Thread Operad Demo ═══\n")

    # Create sample threads
    sample_threads = [
        {
            "id": "T-019b438f-c843-7779-8812-bc0d6fe8b803",
            "title": "Synergistic skill triads and subagent coloring",
            "created": 1766365055043,
            "messageCount": 177,
        },
        {
            "id": "T-019b4388-8d1f-710e-9bce-8cdc3d8ea000",
            "title": "Continue verifying justfile recipes",
            "created": 1766364581152,
            "messageCount": 95,
        },
        {
            "id": "T-019b4364-7514-7758-a42c-fd160b7d2317",
            "title": "Instrumental resources for topos geometric morphisms",
            "created": 1766362215701,
            "messageCount": 145,
        },
    ]

    # Build operad
    operad = build_operad_from_threads(sample_threads, variant="dendroidal")
    if not operad:
        print("Failed to build operad")
        return

    print(f"Operad: {operad.variant.name}, {len(operad.nodes)} nodes\n")

    # GF(3) check
    gf3 = operad.gf3_conservation()
    print(f"GF(3) Conservation: {gf3['conserved']}\n")

    # Show colors
    if use_rich:
        table = Table(title="Thread Colors (3 streams)")
        table.add_column("Thread ID", style="cyan")
        table.add_column("LIVE H°", style="red")
        table.add_column("VERIFY H°", style="green")
        table.add_column("BACKFILL H°", style="blue")
        table.add_column("Trit", style="yellow")

        for tid, node in operad.nodes.items():
            table.add_row(
                tid[:12],
                f"{node.colors['LIVE'].H:.1f}",
                f"{node.colors['VERIFY'].H:.1f}",
                f"{node.colors['BACKFILL'].H:.1f}",
                str(node.trit),
            )
        console.print(table)
    else:
        print("Thread Colors:")
        for tid, node in operad.nodes.items():
            print(f"  {tid[:12]}:")
            print(f"    LIVE:     H={node.colors['LIVE'].H:.1f}° trit={node.trit}")
            print(f"    VERIFY:   H={node.colors['VERIFY'].H:.1f}°")
            print(f"    BACKFILL: H={node.colors['BACKFILL'].H:.1f}°")

    print("\n─── Mermaid Diagram ───")
    print(operad_to_mermaid(operad))

    print("\n─── DisCoPy Structure ───")
    print(json.dumps(operad.to_discopy_diagram(), indent=2))


if __name__ == "__main__":
    main()
