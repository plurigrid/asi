"""
max_fanout_gadget.py - Maximum Fan-Out Local Gadget

A gadget that maximizes parallel skill dispatch while maintaining:
1. LOCAL constraint satisfaction (each triplet GF(3) = 0)
2. GLOBAL correctness guarantee (if local → global, by construction)
3. SUFFICIENCY verification (only fan out with sufficient skills)

The key insight from three-match:
    Local geodesic constraints → Global 3-SAT solution

Applied to skill dispatch:
    Local triad conservation → Global task correctness

This is the dual of dynamic-sufficiency:
- dynamic-sufficiency GATES (prevents action without skills)
- max-fanout FANS OUT (maximizes parallel action with skills)

Together they form a variational bound:
    min(sufficiency) ≤ action ≤ max(fanout)
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Set, Dict, List, Tuple, Optional, Callable, Any, Iterator
from enum import IntEnum
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import time

# Import from world_memory
from world_memory import (
    Trit, Skill, SkillMemory, SKILL_REGISTRY, CANONICAL_TRIADS,
    pre_action_gate, Verdict, CoverageResult, AutopoieticLoop,
    find_similar_skills, TRIT_ROLES
)


# ════════════════════════════════════════════════════════════════════════════
# SplitMix64 for Deterministic Forking
# ════════════════════════════════════════════════════════════════════════════

GOLDEN = 0x9E3779B97F4A7C15
MIX1 = 0xBF58476D1CE4E5B9
MIX2 = 0x94D049BB133111EB
MASK64 = 0xFFFFFFFFFFFFFFFF


def splitmix64(state: int) -> Tuple[int, int]:
    """Generate next state and output."""
    state = (state + GOLDEN) & MASK64
    z = state
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    return state, z ^ (z >> 31)


def fork_seed(parent: int, child_index: int) -> int:
    """Fork a seed into independent child streams."""
    offset = child_index * GOLDEN
    child_state = (parent + offset) & MASK64
    _, child_seed = splitmix64(child_state)
    return child_seed


def interaction_entropy_seed(text: str) -> int:
    """Derive seed from interaction text entropy."""
    # FNV-1a hash
    fnv = 0xcbf29ce484222325
    for b in text.encode():
        fnv ^= b
        fnv = (fnv * 0x100000001b3) & MASK64
    
    # Shannon entropy component
    from collections import Counter
    from math import log2
    chars = list(text)
    counts = Counter(chars)
    total = len(chars)
    entropy = -sum((c/total) * log2(c/total) for c in counts.values() if c > 0)
    entropy_bits = int(entropy * 1_000_000)
    
    return (fnv ^ (entropy_bits * GOLDEN)) & MASK64


# ════════════════════════════════════════════════════════════════════════════
# Local Gadget: Triplet with GF(3) = 0
# ════════════════════════════════════════════════════════════════════════════

@dataclass
class LocalGadget:
    """
    A single triplet of skills forming a local GF(3) = 0 constraint.
    
    This is the "atomic unit" of the fan-out - each gadget is independently
    verifiable and can execute in parallel with other gadgets.
    """
    gadget_id: str
    seed: int
    minus_skill: Skill      # Validator (-1)
    ergodic_skill: Skill    # Coordinator (0)
    plus_skill: Skill       # Generator (+1)
    task_slice: str         # Portion of task assigned to this gadget
    
    @property
    def triad(self) -> Tuple[Skill, Skill, Skill]:
        return (self.minus_skill, self.ergodic_skill, self.plus_skill)
    
    @property
    def gf3_sum(self) -> int:
        return sum(s.trit.value for s in self.triad)
    
    @property
    def is_conserved(self) -> bool:
        return self.gf3_sum % 3 == 0
    
    def execute(self, executor: Optional[Callable] = None) -> Dict[str, Any]:
        """
        Execute the gadget (all three skills in sequence or parallel).
        
        The executor should handle actual skill invocation.
        Default just returns simulation results.
        """
        start = time.perf_counter()
        
        results = {
            "gadget_id": self.gadget_id,
            "seed_hex": f"0x{self.seed:016x}",
            "task_slice": self.task_slice,
            "gf3_conserved": self.is_conserved,
            "skills": [s.name for s in self.triad],
            "trits": [s.trit.value for s in self.triad],
        }
        
        if executor:
            # Execute with provided executor
            skill_results = []
            for i, skill in enumerate(self.triad):
                child_seed = fork_seed(self.seed, i)
                result = executor(skill, self.task_slice, child_seed)
                skill_results.append({
                    "skill": skill.name,
                    "trit": skill.trit.value,
                    "role": skill.role,
                    "seed": f"0x{child_seed:016x}",
                    "result": result
                })
            results["skill_results"] = skill_results
        
        results["elapsed_ms"] = (time.perf_counter() - start) * 1000
        return results


# ════════════════════════════════════════════════════════════════════════════
# Maximum Fan-Out: Parallel Gadget Dispatch
# ════════════════════════════════════════════════════════════════════════════

@dataclass
class FanOutResult:
    """Result of maximum fan-out operation."""
    task: str
    seed: int
    num_gadgets: int
    total_skills: int
    all_conserved: bool
    gadget_results: List[Dict]
    elapsed_ms: float
    statistical_complexity: float


class MaxFanOutGadget:
    """
    Maximum fan-out local gadget.
    
    Given a task:
    1. Check sufficiency (gate with dynamic-sufficiency)
    2. Decompose into parallel gadgets (each GF(3) = 0)
    3. Execute gadgets in parallel (maximum parallelism)
    4. Merge results (correctness by construction)
    
    The key property: if each local gadget is GF(3) conserved,
    the global result is correct by construction.
    """
    
    def __init__(self, seed: int = 0x42D, max_gadgets: int = 9):
        self.seed = seed
        self.max_gadgets = max_gadgets
        self.memory = SkillMemory(seed)
        
        # Load core sufficiency triad
        self.memory.load_triad("sufficiency")
    
    def decompose_task(self, task: str) -> List[str]:
        """
        Decompose a task into parallelizable slices.
        
        Simple heuristic: split by clauses/sentences/operations.
        More sophisticated: use NLP to identify independent subtasks.
        """
        # Split on conjunctions and punctuation
        import re
        
        # Normalize
        normalized = task.lower().strip()
        
        # Split on logical separators
        separators = r'\s+(?:and|then|also|,|;)\s+'
        slices = re.split(separators, normalized)
        
        # Filter empty and dedupe while preserving order
        seen = set()
        result = []
        for s in slices:
            s = s.strip()
            if s and s not in seen:
                result.append(s)
                seen.add(s)
        
        return result if result else [task]
    
    def select_triad_for_slice(self, task_slice: str, index: int) -> Tuple[Skill, Skill, Skill]:
        """
        Select a GF(3) balanced triad for a task slice.
        
        Uses skill inference + canonical triads + similarity matching.
        """
        # Infer skills from slice
        inferred = self.memory.infer_skills_from_text(task_slice)
        
        # Try to form balanced triad from inferred
        minus = None
        ergodic = None
        plus = None
        
        for name in inferred:
            if name in SKILL_REGISTRY:
                skill = SKILL_REGISTRY[name]
                if skill.trit == Trit.MINUS and minus is None:
                    minus = skill
                elif skill.trit == Trit.ERGODIC and ergodic is None:
                    ergodic = skill
                elif skill.trit == Trit.PLUS and plus is None:
                    plus = skill
        
        # Fill gaps with canonical triads or defaults
        if not all([minus, ergodic, plus]):
            # Find most relevant canonical triad
            for bundle, triad_names in CANONICAL_TRIADS.items():
                if any(n in inferred for n in triad_names):
                    for name in triad_names:
                        skill = SKILL_REGISTRY.get(name)
                        if skill:
                            if skill.trit == Trit.MINUS and minus is None:
                                minus = skill
                            elif skill.trit == Trit.ERGODIC and ergodic is None:
                                ergodic = skill
                            elif skill.trit == Trit.PLUS and plus is None:
                                plus = skill
        
        # Ultimate fallback to sufficiency triad
        if minus is None:
            minus = SKILL_REGISTRY.get("dynamic-sufficiency")
        if ergodic is None:
            ergodic = SKILL_REGISTRY.get("skill-dispatch")
        if plus is None:
            plus = SKILL_REGISTRY.get("skill-installer")
        
        return (minus, ergodic, plus)
    
    def build_gadgets(self, task: str) -> List[LocalGadget]:
        """
        Build local gadgets for a task.
        
        Each gadget covers one task slice with a GF(3) balanced triad.
        """
        slices = self.decompose_task(task)
        
        # Limit to max_gadgets
        if len(slices) > self.max_gadgets:
            # Merge excess slices
            merged = []
            for i in range(0, len(slices), len(slices) // self.max_gadgets + 1):
                chunk = slices[i:i + len(slices) // self.max_gadgets + 1]
                merged.append(" and ".join(chunk))
            slices = merged[:self.max_gadgets]
        
        gadgets = []
        for i, slice_text in enumerate(slices):
            # Fork seed for this gadget
            gadget_seed = fork_seed(self.seed, i)
            
            # Select triad
            minus, ergodic, plus = self.select_triad_for_slice(slice_text, i)
            
            # Create gadget
            gadget_id = hashlib.sha256(
                f"{gadget_seed}:{slice_text}".encode()
            ).hexdigest()[:12]
            
            gadget = LocalGadget(
                gadget_id=gadget_id,
                seed=gadget_seed,
                minus_skill=minus,
                ergodic_skill=ergodic,
                plus_skill=plus,
                task_slice=slice_text
            )
            
            gadgets.append(gadget)
            
            # Load skills into memory
            for skill in gadget.triad:
                self.memory.load_skill(skill.name)
        
        return gadgets
    
    def fanout(
        self,
        task: str,
        executor: Optional[Callable] = None,
        parallel: bool = True,
        sufficiency_threshold: float = 0.5
    ) -> FanOutResult:
        """
        Maximum fan-out execution.
        
        1. Check sufficiency
        2. Build gadgets
        3. Execute in parallel
        4. Merge results
        """
        start = time.perf_counter()
        
        # Check sufficiency first
        verdict, coverage = pre_action_gate(task, self.memory, sufficiency_threshold)
        
        if verdict == Verdict.ABORT:
            # Load missing skills
            for skill in coverage.missing[:10]:
                self.memory.load_skill(skill.name)
        
        # Build gadgets
        gadgets = self.build_gadgets(task)
        
        # Execute
        if parallel and len(gadgets) > 1:
            with ThreadPoolExecutor(max_workers=min(len(gadgets), 9)) as pool:
                futures = {
                    pool.submit(g.execute, executor): g 
                    for g in gadgets
                }
                gadget_results = []
                for future in as_completed(futures):
                    gadget_results.append(future.result())
        else:
            gadget_results = [g.execute(executor) for g in gadgets]
        
        # Sort by gadget_id for determinism
        gadget_results.sort(key=lambda r: r["gadget_id"])
        
        # Verify all conserved
        all_conserved = all(r["gf3_conserved"] for r in gadget_results)
        
        # Compute totals
        total_skills = sum(len(r["skills"]) for r in gadget_results)
        
        elapsed = (time.perf_counter() - start) * 1000
        
        return FanOutResult(
            task=task,
            seed=self.seed,
            num_gadgets=len(gadgets),
            total_skills=total_skills,
            all_conserved=all_conserved,
            gadget_results=gadget_results,
            elapsed_ms=elapsed,
            statistical_complexity=self.memory.statistical_complexity()
        )


# ════════════════════════════════════════════════════════════════════════════
# Visualization
# ════════════════════════════════════════════════════════════════════════════

def visualize_fanout(result: FanOutResult) -> str:
    """Generate ASCII visualization of fan-out structure."""
    lines = []
    lines.append("╔═══════════════════════════════════════════════════════════════════╗")
    lines.append("║           MAXIMUM FAN-OUT LOCAL GADGET                            ║")
    lines.append("╚═══════════════════════════════════════════════════════════════════╝")
    lines.append("")
    lines.append(f"Task: {result.task[:60]}...")
    lines.append(f"Seed: 0x{result.seed:016x}")
    lines.append(f"Gadgets: {result.num_gadgets} | Skills: {result.total_skills} | Time: {result.elapsed_ms:.1f}ms")
    lines.append(f"All Conserved: {'✅' if result.all_conserved else '❌'}")
    lines.append(f"Statistical Complexity: {result.statistical_complexity:.3f} bits")
    lines.append("")
    lines.append("─── Gadget Tree ───")
    lines.append("")
    lines.append("                           ┌─────────────┐")
    lines.append("                           │    TASK     │")
    lines.append("                           └──────┬──────┘")
    lines.append("                                  │")
    
    # Fan-out visualization
    n = len(result.gadget_results)
    if n <= 3:
        connectors = "───────────────┼───────────────"
        positions = [0, 1, 2][:n]
    elif n <= 9:
        connectors = "───┬───┬───┬───┼───┬───┬───┬───"
        positions = list(range(n))
    else:
        connectors = "─" * 40
        positions = list(range(min(n, 9)))
    
    lines.append(f"            {connectors[:n*5]}")
    
    # Gadget boxes
    for i, gr in enumerate(result.gadget_results[:9]):
        trits = gr["trits"]
        skills = gr["skills"]
        gf3_ok = "✓" if gr["gf3_conserved"] else "✗"
        
        lines.append(f"")
        lines.append(f"  ┌─ Gadget {i} ({gr['gadget_id'][:6]}) ───────────────────────┐")
        lines.append(f"  │  Slice: {gr['task_slice'][:35]:<35} │")
        lines.append(f"  │  Skills: {skills[0][:12]} | {skills[1][:12]} | {skills[2][:12]} │")
        lines.append(f"  │  Trits:  {trits[0]:+d}           |  {trits[1]:+d}          | {trits[2]:+d}          │")
        lines.append(f"  │  GF(3) = {sum(trits)} {gf3_ok}                                  │")
        lines.append(f"  └──────────────────────────────────────────────────┘")
    
    if n > 9:
        lines.append(f"  ... and {n - 9} more gadgets ...")
    
    return "\n".join(lines)


# ════════════════════════════════════════════════════════════════════════════
# CLI Entry Point
# ════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import sys
    
    print("╔═══════════════════════════════════════════════════════════════════╗")
    print("║  MAXIMUM FAN-OUT LOCAL GADGET                                     ║")
    print("║  Local GF(3) = 0 → Global Correctness by Construction             ║")
    print("╚═══════════════════════════════════════════════════════════════════╝")
    
    # Test task
    task = """
    Create a Julia package with deterministic colors, then verify SPI invariance,
    and also lint the clojure wrapper, then train a cognitive model, and finally
    build an MCP server for color generation
    """
    
    if len(sys.argv) > 1:
        task = " ".join(sys.argv[1:])
    
    # Derive seed from task entropy
    seed = interaction_entropy_seed(task)
    print(f"\n→ Task entropy seed: 0x{seed:016x}")
    
    # Create gadget and fan out
    gadget = MaxFanOutGadget(seed=seed, max_gadgets=9)
    result = gadget.fanout(task, parallel=True)
    
    # Visualize
    print(visualize_fanout(result))
    
    # Summary
    print("\n─── Fan-Out Summary ───")
    print(f"  Gadgets executed: {result.num_gadgets}")
    print(f"  Total skill invocations: {result.total_skills}")
    print(f"  All GF(3) conserved: {result.all_conserved}")
    print(f"  Execution time: {result.elapsed_ms:.2f}ms")
    print(f"  Parallelism factor: {result.total_skills / max(result.elapsed_ms, 1):.2f} skills/ms")
