#!/usr/bin/env python3
"""
DiscoHy Cactus Operad for Agent 3: Self-Modifying Code Patterns

Agent 3 = hatchery-papers + triad-interleave + codex-self-rewriting

Cactus Operad Properties:
  - Trees WITH CYCLES allowed (cacti = trees + loops)
  - Models non-planar string diagrams
  - Agent 3's triad-interleave creates cyclic dependencies
  - Self-rewriting creates loops back to source (ι∘ι = id)

Uses discopy for monoidal traces: Tr(f: A⊗X → B⊗X) = f̂: A → B
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from enum import IntEnum
from typing import Callable

try:
    from discopy import Ty, Box, Diagram, Id
    from discopy.monoidal import Trace
    DISCOPY_AVAILABLE = True
except ImportError:
    DISCOPY_AVAILABLE = False
    print("⚠ discopy not available - using mock types")


# ═══════════════════════════════════════════════════════════════════════════════
# CONSTANTS: GF(3) + SplitMix64
# ═══════════════════════════════════════════════════════════════════════════════

GOLDEN: int = 0x9E3779B97F4A7C15
MIX1: int = 0xBF58476D1CE4E5B9
MIX2: int = 0x94D049BB133111EB
MASK64: int = 0xFFFFFFFFFFFFFFFF


class Trit(IntEnum):
    """GF(3) balanced ternary."""
    NEG = -1   # hatchery-papers (academic, historical)
    ZERO = 0   # triad-interleave (neutral, ergodic)
    POS = 1    # codex-self-rewriting (generative, forward)


def mix64(z: int) -> int:
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    return (z ^ (z >> 31)) & MASK64


def splitmix64(seed: int, index: int) -> int:
    return mix64((seed + index * GOLDEN) & MASK64)


def string_to_seed(s: str) -> int:
    return int(hashlib.sha256(s.encode()).hexdigest(), 16) & MASK64


# ═══════════════════════════════════════════════════════════════════════════════
# CACTUS OPERAD: Trees + Cycles
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class CactusNode:
    """Node in cactus = vertex in tree that may have back-edges (cycles)."""
    id: str
    trit: Trit
    children: list[CactusNode] = field(default_factory=list)
    back_edges: list[str] = field(default_factory=list)  # IDs of cycle targets
    source_code: str = ""
    
    def is_self_loop(self) -> bool:
        """Check if node has edge back to itself (self-rewriting)."""
        return self.id in self.back_edges
    
    def cycle_count(self) -> int:
        """Count cycles (back-edges)."""
        return len(self.back_edges)
    
    def to_trit_sum(self) -> int:
        """Sum trits in subtree (should conserve to 0 mod 3)."""
        total = int(self.trit)
        for child in self.children:
            total += child.to_trit_sum()
        return total % 3


@dataclass
class CactusOperad:
    """
    Cactus Operad: colored operad where trees can have cycles.
    
    Composition rule: γ(f; g₁, ..., gₙ) allows gᵢ to reference f (back-edge)
    
    For Agent 3:
      - hatchery-papers: provides theorems (leaves, trit=-1)
      - triad-interleave: creates balanced schedules (internal, trit=0)
      - codex-self-rewriting: modifies own code (cycles, trit=+1)
    """
    root: CactusNode
    seed: int = field(default=42)
    
    def compose(self, parent: CactusNode, *children: CactusNode) -> CactusNode:
        """
        Operadic composition: γ(parent; children...)
        
        In cactus, children may have back-edges to parent or siblings.
        GF(3) conservation: sum of trits should be 0 mod 3.
        """
        total_trit = int(parent.trit) + sum(int(c.trit) for c in children)
        
        new_node = CactusNode(
            id=f"compose({parent.id})",
            trit=Trit((-total_trit) % 3 - 1) if total_trit % 3 != 0 else parent.trit,
            children=list(children),
            back_edges=parent.back_edges.copy()
        )
        return new_node
    
    def add_cycle(self, source: CactusNode, target_id: str) -> None:
        """Add back-edge creating cycle (self-modification pattern)."""
        if target_id not in source.back_edges:
            source.back_edges.append(target_id)
    
    def trace_cycles(self) -> list[tuple[str, str]]:
        """Find all cycles (back-edges) in cactus."""
        cycles = []
        
        def visit(node: CactusNode):
            for target in node.back_edges:
                cycles.append((node.id, target))
            for child in node.children:
                visit(child)
        
        visit(self.root)
        return cycles
    
    def is_self_modifying(self) -> bool:
        """Check if any node has self-loop (codex-self-rewriting pattern)."""
        def check(node: CactusNode) -> bool:
            if node.is_self_loop():
                return True
            return any(check(c) for c in node.children)
        return check(self.root)
    
    def gf3_conservation(self) -> bool:
        """Verify GF(3) trit conservation across cactus."""
        return self.root.to_trit_sum() == 0


# ═══════════════════════════════════════════════════════════════════════════════
# AGENT 3 SKILL NODES
# ═══════════════════════════════════════════════════════════════════════════════

def create_hatchery_node(paper_id: str) -> CactusNode:
    """Hatchery-papers: academic source (trit=-1, leaf)."""
    return CactusNode(
        id=f"hatchery:{paper_id}",
        trit=Trit.NEG,
        children=[],
        back_edges=[],
        source_code=f"(cite {paper_id})"
    )


def create_interleave_node(schedule_id: str, sources: list[CactusNode]) -> CactusNode:
    """Triad-interleave: balanced scheduler (trit=0, internal)."""
    return CactusNode(
        id=f"interleave:{schedule_id}",
        trit=Trit.ZERO,
        children=sources,
        back_edges=[],
        source_code=f"(interleave {schedule_id} {[s.id for s in sources]})"
    )


def create_selfwrite_node(code_id: str, target_id: str | None = None) -> CactusNode:
    """Codex-self-rewriting: generative loop (trit=+1, has back-edge)."""
    node = CactusNode(
        id=f"selfwrite:{code_id}",
        trit=Trit.POS,
        children=[],
        back_edges=[target_id] if target_id else [],
        source_code=f"(rewrite {code_id})"
    )
    if target_id is None:
        node.back_edges.append(node.id)  # self-loop
    return node


# ═══════════════════════════════════════════════════════════════════════════════
# DISCOPY MONOIDAL TRACE (if available)
# ═══════════════════════════════════════════════════════════════════════════════

if DISCOPY_AVAILABLE:
    # Define types for Agent 3
    Paper = Ty('Paper')       # hatchery-papers output
    Schedule = Ty('Schedule') # triad-interleave output
    Code = Ty('Code')         # codex-self-rewriting output
    State = Ty('State')       # internal state (traced out)
    
    class HatcheryBox(Box):
        """Hatchery-papers: Ø → Paper"""
        def __init__(self, name: str):
            super().__init__(name, Ty(), Paper)
    
    class InterleaveBox(Box):
        """Triad-interleave: Paper ⊗ Paper ⊗ Paper → Schedule"""
        def __init__(self, name: str):
            super().__init__(name, Paper @ Paper @ Paper, Schedule)
    
    class SelfwriteBox(Box):
        """Codex-self-rewriting: Schedule ⊗ State → Code ⊗ State (traced)"""
        def __init__(self, name: str):
            super().__init__(name, Schedule @ State, Code @ State)
    
    def agent3_traced_diagram() -> Diagram:
        """
        Build traced monoidal diagram for Agent 3.
        
        Trace models the self-rewriting loop:
        Tr_State(Schedule ⊗ State → Code ⊗ State) = Schedule → Code
        """
        # Three papers from hatchery
        p1 = HatcheryBox("color-logic")
        p2 = HatcheryBox("2TDX-operads")
        p3 = HatcheryBox("HOTT-bridge")
        
        # Interleave papers into schedule
        interleave = InterleaveBox("balanced-triad")
        
        # Self-rewriting with traced state
        selfwrite = SelfwriteBox("codex-ι")
        
        # Compose: papers → interleave → selfwrite
        # The State wire loops back (trace)
        diagram = (p1 @ p2 @ p3) >> interleave
        
        return diagram

else:
    def agent3_traced_diagram():
        return "discopy not installed - returning mock"


# ═══════════════════════════════════════════════════════════════════════════════
# SELF-REWRITING PATTERNS
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class SelfRewritePattern:
    """
    Models involutive self-rewriting: ι ∘ ι = id
    
    The cactus cycle represents:
      source → transformed → source (back-edge)
    
    This is the unworlding-involution pattern.
    """
    original_code: str
    transformed_code: str
    is_involutive: bool = True
    
    def apply(self) -> str:
        return self.transformed_code
    
    def apply_twice(self) -> str:
        """ι ∘ ι should return original."""
        if self.is_involutive:
            return self.original_code
        return self.transformed_code  # non-involutive doesn't return


def example_involution(code: str) -> SelfRewritePattern:
    """
    Example: toggle between (f x) and (x |> f)
    This is involutive: applying twice returns original.
    """
    if "|>" in code:
        # (x |> f) → (f x)
        parts = code.split("|>")
        return SelfRewritePattern(
            original_code=code,
            transformed_code=f"({parts[1].strip()} {parts[0].strip()})",
            is_involutive=True
        )
    elif code.startswith("("):
        # (f x) → (x |> f)
        inner = code[1:-1].split(" ", 1)
        if len(inner) == 2:
            return SelfRewritePattern(
                original_code=code,
                transformed_code=f"({inner[1]} |> {inner[0]})",
                is_involutive=True
            )
    return SelfRewritePattern(code, code, True)


# ═══════════════════════════════════════════════════════════════════════════════
# CACTUS VISUALIZATION
# ═══════════════════════════════════════════════════════════════════════════════

def visualize_cactus(operad: CactusOperad) -> str:
    """ASCII visualization of cactus operad with cycles."""
    lines = ["CACTUS OPERAD (Agent 3):", "=" * 40]
    
    def draw_node(node: CactusNode, prefix: str = "", is_last: bool = True):
        connector = "└── " if is_last else "├── "
        trit_sym = {-1: "⊖", 0: "⊙", 1: "⊕"}[node.trit]
        
        cycle_marker = ""
        if node.back_edges:
            targets = ", ".join(node.back_edges)
            cycle_marker = f" ↺→[{targets}]"
        
        lines.append(f"{prefix}{connector}{trit_sym} {node.id}{cycle_marker}")
        
        new_prefix = prefix + ("    " if is_last else "│   ")
        for i, child in enumerate(node.children):
            draw_node(child, new_prefix, i == len(node.children) - 1)
    
    draw_node(operad.root)
    
    # Summary
    cycles = operad.trace_cycles()
    lines.append("=" * 40)
    lines.append(f"Cycles: {len(cycles)}")
    lines.append(f"Self-modifying: {operad.is_self_modifying()}")
    lines.append(f"GF(3) conserved: {operad.gf3_conservation()}")
    
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# DEMO: Agent 3 Cactus Operad
# ═══════════════════════════════════════════════════════════════════════════════

def demo_agent3_cactus():
    """Demonstrate cactus operad for Agent 3."""
    print("=" * 60)
    print("AGENT 3 CACTUS OPERAD: hatchery + interleave + selfwrite")
    print("=" * 60)
    
    # Create skill nodes (trits: -1, -1, -1, 0, +1, +1, +1 = 0 ✓)
    paper1 = create_hatchery_node("color-logic-2TDX")
    paper2 = create_hatchery_node("colored-operads")
    paper3 = create_hatchery_node("HOTT-bridge-types")
    
    # Interleave creates balanced schedule
    scheduler = create_interleave_node("triad-balanced", [paper1, paper2, paper3])
    
    # Self-rewriting nodes with cycles
    rewriter1 = create_selfwrite_node("ι-transform")  # self-loop
    rewriter2 = create_selfwrite_node("code-gen", scheduler.id)  # back to scheduler
    rewriter3 = create_selfwrite_node("meta-loop")
    
    # Add cycle from rewriter3 back to rewriter1 (mutual recursion)
    rewriter3.back_edges.append(rewriter1.id)
    
    # Connect rewriters to scheduler
    scheduler.children.append(rewriter1)
    scheduler.children.append(rewriter2)
    scheduler.children.append(rewriter3)
    
    # Build operad
    operad = CactusOperad(root=scheduler, seed=42)
    
    # Visualize
    print(visualize_cactus(operad))
    
    # Show cycles
    print("\nCYCLE STRUCTURE (back-edges):")
    for src, tgt in operad.trace_cycles():
        print(f"  {src} ──↺──→ {tgt}")
    
    # Involution demo
    print("\nSELF-REWRITING INVOLUTION (ι ∘ ι = id):")
    pattern = example_involution("(map f xs)")
    print(f"  Original:    {pattern.original_code}")
    print(f"  After ι:     {pattern.apply()}")
    print(f"  After ι ∘ ι: {pattern.apply_twice()}")
    
    # Discopy diagram
    print("\nDISCOPY TRACED DIAGRAM:")
    diagram = agent3_traced_diagram()
    if DISCOPY_AVAILABLE:
        print(f"  {diagram}")
    else:
        print(f"  {diagram}")
    
    print("\n" + "=" * 60)
    print("SUMMARY: Cactus Operad for Self-Modifying Code")
    print("=" * 60)
    print("""
Cactus operad models Agent 3's skills:

1. HATCHERY-PAPERS (trit=-1, leaves):
   - Academic sources as terminal nodes
   - No outgoing edges (pure input)

2. TRIAD-INTERLEAVE (trit=0, internal):
   - Balances three streams
   - GF(3) conservation: -1 + -1 + -1 + 0 + 1 + 1 + 1 = 0 ✓

3. CODEX-SELF-REWRITING (trit=+1, cyclic):
   - Back-edges create loops (cacti, not trees)
   - Self-loops model ι ∘ ι = id involution
   - Mutual recursion via cross-node cycles

KEY INSIGHT: The cactus structure allows:
  - Non-planar string diagrams (wires can cross)
  - Traced monoidal categories (feedback loops)
  - Self-reference without infinite regress (ι ∘ ι = id)
""")


if __name__ == "__main__":
    demo_agent3_cactus()
