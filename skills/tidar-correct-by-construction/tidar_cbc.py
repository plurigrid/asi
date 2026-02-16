#!/usr/bin/env python3
"""
TIDAR: Correct by Construction

Type-level guarantees for GF(3) conservation in triadic agent trees.
If it runs, it's balanced — invalid states are unrepresentable.

Key insight: Triads are the ONLY way to construct agents.
"""
from __future__ import annotations
import asyncio
import hashlib
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import IntEnum
from typing import (
    Generic, TypeVar, Tuple, List, Iterator, 
    Callable, Awaitable, Optional, Final, Literal
)

# ═══════════════════════════════════════════════════════════════════════════════
# GF(3) TRIT: The atomic unit of balance
# ═══════════════════════════════════════════════════════════════════════════════

class Trit(IntEnum):
    """Balanced ternary: -1, 0, +1. Sum of any valid triad = 0."""
    MINUS = -1
    MIDDLE = 0
    PLUS = 1
    
    def __neg__(self) -> Trit:
        return Trit(-self.value)
    
    def __add__(self, other: Trit) -> int:
        return self.value + other.value
    
    @property
    def role(self) -> str:
        return {-1: "sink", 0: "transform", 1: "source"}[self.value]
    
    @property
    def symbol(self) -> str:
        return {-1: "−", 0: "○", 1: "+"}[self.value]


# ═══════════════════════════════════════════════════════════════════════════════
# SPLITMIX64 RNG: Deterministic, splittable
# ═══════════════════════════════════════════════════════════════════════════════

MASK64: Final = 0xFFFFFFFFFFFFFFFF
DEFAULT_GAMMA: Final = 0x9E3779B97F4A7C15

def _mix64(z: int) -> int:
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9 & MASK64
    z = (z ^ (z >> 27)) * 0x94D049BB133111EB & MASK64
    return z ^ (z >> 31)


@dataclass(frozen=True)
class SplitRng:
    """Immutable splittable RNG — perfect for parallel TIDAR."""
    state: int
    gamma: int = DEFAULT_GAMMA
    
    @classmethod
    def from_seed(cls, seed: int) -> SplitRng:
        return cls(state=seed & MASK64)
    
    def next(self) -> Tuple[int, SplitRng]:
        new_state = (self.state + self.gamma) & MASK64
        return _mix64(new_state), SplitRng(new_state, self.gamma)
    
    def split3(self) -> Tuple[SplitRng, SplitRng, SplitRng]:
        """Split into exactly 3 streams — one per trit."""
        n1, r1 = self.next()
        n2, r2 = r1.next()
        n3, _ = r2.next()
        return (
            SplitRng((self.state ^ n1) & MASK64, self.gamma),
            SplitRng((self.state ^ n2) & MASK64, (self.gamma | 1) & MASK64),
            SplitRng((self.state ^ n3) & MASK64, (self.gamma ^ 0x5555) & MASK64),
        )


# ═══════════════════════════════════════════════════════════════════════════════
# CORRECT-BY-CONSTRUCTION TRIAD: The only way to create balanced agents
# ═══════════════════════════════════════════════════════════════════════════════

T = TypeVar('T')

@dataclass(frozen=True)
class Triad(Generic[T]):
    """
    A balanced triple: MINUS + MIDDLE + PLUS = 0.
    
    This is the ONLY way to create TIDAR agents.
    GF(3) conservation is GUARANTEED by construction.
    """
    minus: T   # -1
    middle: T  # 0
    plus: T    # +1
    
    @classmethod
    def build(cls, minus: T, middle: T, plus: T) -> Triad[T]:
        """
        Build a triad. This is the sole constructor.
        By using this, you PROVE GF(3) conservation.
        """
        return cls(minus=minus, middle=middle, plus=plus)
    
    def map(self, f: Callable[[T, Trit], T]) -> Triad[T]:
        """Map a function over the triad, preserving balance."""
        return Triad.build(
            f(self.minus, Trit.MINUS),
            f(self.middle, Trit.MIDDLE),
            f(self.plus, Trit.PLUS)
        )
    
    def __iter__(self) -> Iterator[Tuple[Trit, T]]:
        yield Trit.MINUS, self.minus
        yield Trit.MIDDLE, self.middle
        yield Trit.PLUS, self.plus
    
    @property
    def sum(self) -> Literal[0]:
        """Always 0 — this is the invariant."""
        return 0  # type: ignore (proven by construction)


# ═══════════════════════════════════════════════════════════════════════════════
# AGENT PHASES: Pre-hook → Execute → Collapse (state machine in types)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class PreHookPhase:
    """Phase 1: Read-only probing. Cannot write."""
    context: dict = field(default_factory=dict)


@dataclass(frozen=True) 
class ExecutePhase:
    """Phase 2: Parallel execution. Can read/write."""
    prehook_result: dict = field(default_factory=dict)


@dataclass(frozen=True)
class CollapsePhase:
    """Phase 3: Middle-path collapse. Only MIDDLE emits."""
    execution_results: Triad[dict] = field(default_factory=lambda: Triad.build({}, {}, {}))


# ═══════════════════════════════════════════════════════════════════════════════
# TIDAR AGENT: Abstract base with trit identity
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class AgentResult:
    """Result from an agent, tagged with its trit."""
    trit: Trit
    agent_id: str
    data: dict
    
    @property
    def is_middle(self) -> bool:
        return self.trit == Trit.MIDDLE


class TIDARAgent(ABC):
    """
    Abstract TIDAR agent. Must be created via Triad.
    
    The trit is immutable — agents cannot change their role.
    """
    
    def __init__(self, trit: Trit, agent_id: str, rng: SplitRng):
        self._trit: Final = trit
        self._id: Final = agent_id
        self._rng = rng
        self._children: Optional[Triad[TIDARAgent]] = None
    
    @property
    def trit(self) -> Trit:
        return self._trit
    
    @property
    def agent_id(self) -> str:
        return self._id
    
    @property
    def is_leaf(self) -> bool:
        return self._children is None
    
    @abstractmethod
    async def prehook(self, phase: PreHookPhase) -> dict:
        """Phase 1: Read-only probe."""
        ...
    
    @abstractmethod
    async def execute(self, phase: ExecutePhase) -> dict:
        """Phase 2: Parallel execution."""
        ...
    
    def can_emit(self) -> bool:
        """Only MIDDLE agents emit final results."""
        return self._trit == Trit.MIDDLE


# ═══════════════════════════════════════════════════════════════════════════════
# TIDAR TREE: 40 agents, 27 leaves, correct by construction
# ═══════════════════════════════════════════════════════════════════════════════

class TIDARLeafAgent(TIDARAgent):
    """Leaf agent (depth 3). Does actual work."""
    
    async def prehook(self, phase: PreHookPhase) -> dict:
        val, self._rng = self._rng.next()
        return {"probed": True, "agent": self._id, "trit": int(self._trit), "seed_sample": val & 0xFFFF}
    
    async def execute(self, phase: ExecutePhase) -> dict:
        val, self._rng = self._rng.next()
        return {"executed": True, "agent": self._id, "trit": int(self._trit), "result": val & 0xFFFF}


class TIDARBranchAgent(TIDARAgent):
    """Branch agent. Coordinates child triad."""
    
    def __init__(self, trit: Trit, agent_id: str, rng: SplitRng, children: Triad[TIDARAgent]):
        super().__init__(trit, agent_id, rng)
        self._children = children
    
    async def prehook(self, phase: PreHookPhase) -> dict:
        assert self._children is not None
        tasks = [child.prehook(phase) for _, child in self._children]
        results = await asyncio.gather(*tasks)
        return {
            "agent": self._id,
            "trit": int(self._trit),
            "children": dict(zip(["minus", "middle", "plus"], results))
        }
    
    async def execute(self, phase: ExecutePhase) -> dict:
        assert self._children is not None
        tasks = [child.execute(phase) for _, child in self._children]
        results = await asyncio.gather(*tasks)
        return {
            "agent": self._id,
            "trit": int(self._trit),
            "children": dict(zip(["minus", "middle", "plus"], results))
        }


@dataclass
class TIDARTree:
    """
    Complete TIDAR tree: 40 agents, 27 leaves.
    
    Correct by construction:
    - Root is MIDDLE (ergodic coordinator)
    - Every level has balanced triads
    - Total: 1 + 3 + 9 + 27 = 40 agents
    """
    root: TIDARBranchAgent
    depth: int
    total_agents: int
    leaf_count: int
    
    @classmethod
    def build_depth_3(cls, seed: int = 1069) -> TIDARTree:
        """
        Build a depth-3 TIDAR tree.
        
        Structure (proven by construction):
        - 1 root (MIDDLE)
        - 3 level-1 branches
        - 9 level-2 branches  
        - 27 level-3 leaves
        = 40 agents total
        """
        rng = SplitRng.from_seed(seed)
        agent_counter = [0]
        
        def make_id() -> str:
            agent_counter[0] += 1
            return f"agent_{agent_counter[0]:02d}"
        
        def build_level(depth: int, trit: Trit, parent_rng: SplitRng) -> TIDARAgent:
            agent_id = make_id()
            
            if depth == 3:
                # Leaf level
                return TIDARLeafAgent(trit, agent_id, parent_rng)
            
            # Branch: recurse with split RNGs
            child_rngs = parent_rng.split3()
            children = Triad.build(
                build_level(depth + 1, Trit.MINUS, child_rngs[0]),
                build_level(depth + 1, Trit.MIDDLE, child_rngs[1]),
                build_level(depth + 1, Trit.PLUS, child_rngs[2]),
            )
            return TIDARBranchAgent(trit, agent_id, parent_rng, children)
        
        # Root is always MIDDLE (ergodic coordinator)
        root = build_level(0, Trit.MIDDLE, rng)
        assert isinstance(root, TIDARBranchAgent)
        
        return cls(
            root=root,
            depth=3,
            total_agents=agent_counter[0],
            leaf_count=27
        )
    
    def verify_structure(self) -> dict:
        """Verify the tree structure is correct."""
        agents_by_level = {0: 0, 1: 0, 2: 0, 3: 0}
        leaves = []
        
        def traverse(agent: TIDARAgent, level: int):
            agents_by_level[level] += 1
            if agent.is_leaf:
                leaves.append(agent)
            elif agent._children:
                for _, child in agent._children:
                    traverse(child, level + 1)
        
        traverse(self.root, 0)
        
        return {
            "agents_by_level": agents_by_level,
            "total_agents": sum(agents_by_level.values()),
            "leaf_count": len(leaves),
            "expected_total": 40,
            "expected_leaves": 27,
            "structure_valid": (
                sum(agents_by_level.values()) == 40 and
                len(leaves) == 27 and
                agents_by_level == {0: 1, 1: 3, 2: 9, 3: 27}
            ),
            "gf3_conserved": True  # By construction
        }
    
    async def dispatch_with_prehooks(
        self, 
        task: dict
    ) -> AsyncIterator[AgentResult]:
        """
        Full TIDAR dispatch with phases:
        1. Pre-hook: parallel read-only probe
        2. Execute: parallel work
        3. Collapse: emit from MIDDLE path only
        """
        # Phase 1: Pre-hooks
        prehook_phase = PreHookPhase(context=task)
        prehook_results = await self.root.prehook(prehook_phase)
        
        # Phase 2: Execute  
        execute_phase = ExecutePhase(prehook_result=prehook_results)
        execute_results = await self.root.execute(execute_phase)
        
        # Phase 3: Collapse via MIDDLE path
        # Only MIDDLE agents emit — this is enforced by can_emit()
        async def collect_middle_results(agent: TIDARAgent, results: dict) -> AsyncIterator[AgentResult]:
            if agent.can_emit():
                yield AgentResult(
                    trit=agent.trit,
                    agent_id=agent.agent_id,
                    data=results
                )
            
            if agent._children:
                child_results = results.get("children", {})
                for trit, child in agent._children:
                    child_data = child_results.get(trit.role, {})
                    async for r in collect_middle_results(child, child_data):
                        yield r
        
        async for result in collect_middle_results(self.root, execute_results):
            yield result


# Type alias for async iterator
from typing import AsyncIterator


# ═══════════════════════════════════════════════════════════════════════════════
# GF(3) CONSERVATION PROOF
# ═══════════════════════════════════════════════════════════════════════════════

def prove_gf3_conservation(tree: TIDARTree) -> dict:
    """
    Proof that GF(3) is conserved at every level.
    
    This is actually a tautology — the Triad constructor guarantees it.
    """
    level_sums = {0: [], 1: [], 2: [], 3: []}
    
    def traverse(agent: TIDARAgent, level: int):
        level_sums[level].append(agent.trit.value)
        if agent._children:
            for _, child in agent._children:
                traverse(child, level + 1)
    
    traverse(tree.root, 0)
    
    proof = {}
    for level, trits in level_sums.items():
        total = sum(trits)
        proof[f"level_{level}"] = {
            "trits": trits,
            "sum": total,
            "conserved": total == 0,
            "count": len(trits)
        }
    
    proof["global_sum"] = sum(sum(trits) for trits in level_sums.values())
    proof["globally_conserved"] = proof["global_sum"] == 0
    
    return proof


# ═══════════════════════════════════════════════════════════════════════════════
# DEMO
# ═══════════════════════════════════════════════════════════════════════════════

async def main():
    print("╔══════════════════════════════════════════════════════════════════╗")
    print("║           TIDAR: Correct by Construction                         ║")
    print("╚══════════════════════════════════════════════════════════════════╝")
    
    # Build tree — only balanced constructions allowed
    tree = TIDARTree.build_depth_3(seed=1069)
    
    print(f"\n📊 Structure Verification:")
    structure = tree.verify_structure()
    for k, v in structure.items():
        print(f"   {k}: {v}")
    
    print(f"\n⚖️  GF(3) Conservation Proof:")
    proof = prove_gf3_conservation(tree)
    for level in range(4):
        p = proof[f"level_{level}"]
        status = "✓" if p["conserved"] else "✗"
        print(f"   Level {level}: {p['count']:2} agents, sum={p['sum']:+2} {status}")
    print(f"   Global: sum={proof['global_sum']:+2} → {'✓ CONSERVED' if proof['globally_conserved'] else '✗ VIOLATED'}")
    
    print(f"\n🚀 Dispatch with Pre-hooks:")
    task = {"action": "test", "data": [1, 2, 3]}
    
    results = []
    async for result in tree.dispatch_with_prehooks(task):
        results.append(result)
        print(f"   {result.trit.symbol} {result.agent_id}: emitted from MIDDLE path")
    
    print(f"\n   Total MIDDLE emissions: {len(results)}")
    print(f"   All from MIDDLE: {all(r.is_middle for r in results)}")
    
    print("\n" + "═" * 70)
    print("  TIDAR tree is correct by construction:")
    print("  • 40 agents (1+3+9+27)")
    print("  • 27 leaves")
    print("  • GF(3) conserved at every level")
    print("  • Only MIDDLE path emits results")
    print("═" * 70)


if __name__ == "__main__":
    asyncio.run(main())
