#!/usr/bin/env python3
"""
Relational Operad Interleaving via DiscoHy + ACSets

This module interleaves the 7 DiscoHy operad implementations using:
1. ACSet relational thinking (functors C → Set)
2. Triad interleaving (GF(3) conservation)
3. Success pattern tracking via DuckDB

The 7 Operads form a SCHEMA (small category):
  LittleDisks ──→ Cubes ──→ SwissCheese
       │           │            │
       ↓           ↓            ↓
    Cactus ──→ Thread ──→ Modular
                  │
                  ↓
              Gravity

Relations (morphisms) encode how operads compose.
"""

from __future__ import annotations

import json
import hashlib
from dataclasses import dataclass, field
from enum import IntEnum
from pathlib import Path
from typing import Any, Callable, Iterator
from datetime import datetime

# ═══════════════════════════════════════════════════════════════════════════════
# GF(3) TRIT SYSTEM
# ═══════════════════════════════════════════════════════════════════════════════

class Trit(IntEnum):
    MINUS = -1    # Structure, conservation
    ERGODIC = 0   # Neutral, verification
    PLUS = 1      # Generative, forward

GOLDEN = 0x9E3779B97F4A7C15
MASK64 = 0xFFFFFFFFFFFFFFFF


def splitmix64(seed: int, index: int) -> int:
    """Deterministic color from seed at index."""
    z = (seed + index * GOLDEN) & MASK64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    return (z ^ (z >> 31)) & MASK64


# ═══════════════════════════════════════════════════════════════════════════════
# ACSET SCHEMA: Operad Relational Structure
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class OperadObject:
    """Object in the operad schema category."""
    name: str
    file: str
    trit: int
    dimension: int  # E_n dimension or genus
    skill_triad: tuple[str, str, str]
    
    @property
    def gf3_sum(self) -> int:
        """GF(3) sum of skill triad trits."""
        # Each skill has an implicit trit - we derive from name hash
        return sum(hash(s) % 3 - 1 for s in self.skill_triad) % 3


@dataclass 
class OperadMorphism:
    """Morphism between operads (structure-preserving map)."""
    source: str
    target: str
    morphism_type: str  # "embedding", "quotient", "stabilization", "forgetting"
    preserves_gf3: bool = True
    

# The 7 DiscoHy Operads as ACSet Objects
OPERAD_OBJECTS: dict[str, OperadObject] = {
    "little_disks": OperadObject(
        name="E_2 Little Disks",
        file="discohy_operad_1_little_disks.py",
        trit=Trit.PLUS,
        dimension=2,
        skill_triad=("rama-gay-clojure", "localsend-mcp", "geiser-chicken"),
    ),
    "cubes": OperadObject(
        name="E_∞ Cubes", 
        file="discohy_operad_2_cubes.py",
        trit=Trit.MINUS,  # Changed: -1 for GF(3) balance
        dimension=float('inf'),
        skill_triad=("xenodium-elisp", "tailscale-file-transfer", "parallel-fanout"),
    ),
    "cactus": OperadObject(
        name="Cactus Operad",
        file="discohy_operad_3_cactus.py",
        trit=Trit.MINUS,
        dimension=1,  # Trees with cycles
        skill_triad=("hatchery-papers", "triad-interleave", "codex-self-rewriting"),
    ),
    "thread": OperadObject(
        name="Thread Operad",
        file="discohy_operad_4_thread.py",
        trit=Trit.ERGODIC,
        dimension=1,  # Linear threads
        skill_triad=("codex-self-rewriting", "bisimulation-game", "duckdb-ies"),
    ),
    "gravity": OperadObject(
        name="Gravity Operad",
        file="discohy_operad_5_gravity.lisp",
        trit=Trit.MINUS,
        dimension=0,  # M_{0,n} genus 0
        skill_triad=("slime-lisp", "asi-integrated", "unworlding-involution"),
    ),
    "modular": OperadObject(
        name="Modular Operad",
        file="discohy_operad_6_modular.bb",
        trit=Trit.PLUS,
        dimension=-1,  # All genera
        skill_triad=("squint-runtime", "borkdude", "geiser-chicken"),
    ),
    "swiss_cheese": OperadObject(
        name="Swiss-Cheese Operad",
        file="discohy_operad_7_swiss_cheese.py",
        trit=Trit.PLUS,
        dimension=2,  # Open + closed disks
        skill_triad=("forward-forward-learning", "xenodium-elisp", "proofgeneral-narya"),
    ),
}

# Morphisms between operads (the relational structure)
OPERAD_MORPHISMS: list[OperadMorphism] = [
    # E_n stabilization: E_2 → E_∞
    OperadMorphism("little_disks", "cubes", "stabilization"),
    
    # Forget cyclic structure: Cactus → Thread
    OperadMorphism("cactus", "thread", "forgetting"),
    
    # Genus restriction: Modular → Gravity (restrict to genus 0)
    OperadMorphism("modular", "gravity", "quotient"),
    
    # Open/closed splitting: Swiss-Cheese relates to E_2
    OperadMorphism("swiss_cheese", "little_disks", "embedding"),
    
    # Thread operad is central hub
    OperadMorphism("little_disks", "thread", "linearization"),
    OperadMorphism("cubes", "thread", "linearization"),
    OperadMorphism("gravity", "thread", "embedding"),
    
    # Modular covers everything
    OperadMorphism("modular", "cactus", "embedding"),
    OperadMorphism("modular", "swiss_cheese", "embedding"),
]


# ═══════════════════════════════════════════════════════════════════════════════
# ACSET: Functor from Schema to Set
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class OperadACSet:
    """
    ACSet representation of operad network.
    
    This is a functor X: SchOperad → Set where:
    - X(Operad) = set of 7 operad objects
    - X(Morphism) = set of structure-preserving maps
    - X(src), X(tgt): morphisms → operads
    """
    
    operads: dict[str, OperadObject] = field(default_factory=lambda: OPERAD_OBJECTS.copy())
    morphisms: list[OperadMorphism] = field(default_factory=lambda: OPERAD_MORPHISMS.copy())
    success_log: list[dict] = field(default_factory=list)
    seed: int = 0x42D
    
    def parts(self, ob_type: str) -> list:
        """Get all parts of given type (ACSet interface)."""
        if ob_type == "Operad":
            return list(self.operads.values())
        elif ob_type == "Morphism":
            return self.morphisms
        return []
    
    def src(self, morphism: OperadMorphism) -> OperadObject:
        """Source of morphism."""
        return self.operads[morphism.source]
    
    def tgt(self, morphism: OperadMorphism) -> OperadObject:
        """Target of morphism."""
        return self.operads[morphism.target]
    
    def gf3_total(self) -> int:
        """Total GF(3) balance of all operads."""
        return sum(op.trit for op in self.operads.values()) % 3
    
    def neighbors(self, operad_key: str) -> list[str]:
        """Get neighboring operads via morphisms."""
        nbrs = []
        for m in self.morphisms:
            if m.source == operad_key:
                nbrs.append(m.target)
            elif m.target == operad_key:
                nbrs.append(m.source)
        return list(set(nbrs))


# ═══════════════════════════════════════════════════════════════════════════════
# TRIAD INTERLEAVING: 3-Way Parallel Execution
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class TriadSchedule:
    """
    Interleaved schedule of 3 operad streams.
    
    Invariant: Each triplet sums to 0 mod 3 (GF(3) conservation).
    """
    
    stream_minus: list[str]   # MINUS operads: cactus, gravity
    stream_ergodic: list[str] # ERGODIC operads: cubes, thread
    stream_plus: list[str]    # PLUS operads: little_disks, modular, swiss_cheese
    schedule: list[tuple[str, str, str]] = field(default_factory=list)
    
    def build_round_robin(self, n_triplets: int) -> list[tuple[str, str, str]]:
        """Build round-robin interleaved schedule."""
        self.schedule = []
        
        for i in range(n_triplets):
            minus = self.stream_minus[i % len(self.stream_minus)] if self.stream_minus else "gravity"
            ergodic = self.stream_ergodic[i % len(self.stream_ergodic)] if self.stream_ergodic else "thread"
            plus = self.stream_plus[i % len(self.stream_plus)] if self.stream_plus else "little_disks"
            
            self.schedule.append((minus, ergodic, plus))
        
        return self.schedule
    
    def verify_gf3(self) -> bool:
        """Verify all triplets conserve GF(3)."""
        for minus, ergodic, plus in self.schedule:
            m_trit = OPERAD_OBJECTS.get(minus, OPERAD_OBJECTS["gravity"]).trit
            e_trit = OPERAD_OBJECTS.get(ergodic, OPERAD_OBJECTS["thread"]).trit
            p_trit = OPERAD_OBJECTS.get(plus, OPERAD_OBJECTS["little_disks"]).trit
            
            if (m_trit + e_trit + p_trit) % 3 != 0:
                return False
        return True


def build_triad_from_operads() -> TriadSchedule:
    """Build triad schedule from the 7 operads."""
    minus_ops = [k for k, v in OPERAD_OBJECTS.items() if v.trit == Trit.MINUS]
    ergodic_ops = [k for k, v in OPERAD_OBJECTS.items() if v.trit == Trit.ERGODIC]
    plus_ops = [k for k, v in OPERAD_OBJECTS.items() if v.trit == Trit.PLUS]
    
    return TriadSchedule(
        stream_minus=minus_ops,
        stream_ergodic=ergodic_ops,
        stream_plus=plus_ops,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# SUCCESS PATTERN TRACKING
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class SuccessPattern:
    """Track successful operad compositions."""
    
    operad_key: str
    execution_time_ms: float
    gf3_conserved: bool
    artifacts_created: list[str]
    timestamp: str = field(default_factory=lambda: datetime.now().isoformat())
    color_hex: str = ""
    
    def __post_init__(self):
        if not self.color_hex:
            h = splitmix64(hash(self.operad_key), 0)
            r = (h >> 16) & 0xFF
            g = (h >> 8) & 0xFF
            b = h & 0xFF
            self.color_hex = f"#{r:02x}{g:02x}{b:02x}"


class SuccessTracker:
    """Track and query success patterns via relational structure."""
    
    def __init__(self, acset: OperadACSet):
        self.acset = acset
        self.patterns: list[SuccessPattern] = []
    
    def log_success(self, operad_key: str, time_ms: float, artifacts: list[str]):
        """Log a successful operad execution."""
        pattern = SuccessPattern(
            operad_key=operad_key,
            execution_time_ms=time_ms,
            gf3_conserved=self.acset.gf3_total() == 0,
            artifacts_created=artifacts,
        )
        self.patterns.append(pattern)
        self.acset.success_log.append({
            "operad": operad_key,
            "time_ms": time_ms,
            "gf3": pattern.gf3_conserved,
            "color": pattern.color_hex,
            "timestamp": pattern.timestamp,
        })
        return pattern
    
    def query_by_trit(self, trit: int) -> list[SuccessPattern]:
        """Query successes by trit polarity."""
        return [p for p in self.patterns 
                if OPERAD_OBJECTS.get(p.operad_key, OperadObject("", "", 0, 0, ("","",""))).trit == trit]
    
    def to_duckdb_insert(self) -> str:
        """Generate DuckDB INSERT statements for success log."""
        if not self.patterns:
            return "-- No patterns to insert"
        
        lines = ["INSERT INTO operad_success VALUES"]
        for i, p in enumerate(self.patterns):
            comma = "," if i < len(self.patterns) - 1 else ";"
            lines.append(f"  ('{p.operad_key}', {p.execution_time_ms}, {p.gf3_conserved}, "
                        f"'{p.color_hex}', '{p.timestamp}'){comma}")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# RELATIONAL COMPOSITION: Operad × Operad → Operad
# ═══════════════════════════════════════════════════════════════════════════════

def compose_operads(op1: OperadObject, op2: OperadObject, morphism: OperadMorphism) -> dict:
    """
    Compose two operads along a morphism.
    
    Returns composition metadata including:
    - Combined trit (sum mod 3)
    - New dimension (max of both)
    - Merged skill triad
    """
    return {
        "source": op1.name,
        "target": op2.name,
        "morphism_type": morphism.morphism_type,
        "combined_trit": (op1.trit + op2.trit) % 3,
        "dimension": max(op1.dimension, op2.dimension) if op2.dimension != float('inf') else float('inf'),
        "skills": list(set(op1.skill_triad) | set(op2.skill_triad)),
        "gf3_preserved": morphism.preserves_gf3,
    }


def compute_all_compositions(acset: OperadACSet) -> list[dict]:
    """Compute all operad compositions from morphisms."""
    compositions = []
    for m in acset.morphisms:
        src = acset.src(m)
        tgt = acset.tgt(m)
        compositions.append(compose_operads(src, tgt, m))
    return compositions


# ═══════════════════════════════════════════════════════════════════════════════
# DISCOPY DIAGRAM GENERATION
# ═══════════════════════════════════════════════════════════════════════════════

def to_discopy_monoidal(acset: OperadACSet) -> str:
    """Generate DisCoPy code for the operad network as monoidal diagram."""
    lines = [
        "# DisCoPy Monoidal Diagram for Operad Network",
        "# Generated from relational ACSet structure",
        "",
        "try:",
        "    from discopy.monoidal import Ty, Box, Id",
        "    from discopy.drawing import draw",
        "    DISCOPY = True",
        "except ImportError:",
        "    DISCOPY = False",
        "",
        "if DISCOPY:",
        "    # Types for each operad",
    ]
    
    # Define types
    for key, op in acset.operads.items():
        lines.append(f"    {key} = Ty('{op.name}')")
    
    lines.append("")
    lines.append("    # Boxes for morphisms")
    
    # Define boxes for morphisms
    for i, m in enumerate(acset.morphisms):
        src_type = m.source
        tgt_type = m.target
        lines.append(f"    m{i} = Box('{m.morphism_type}', {src_type}, {tgt_type})")
    
    lines.append("")
    lines.append("    # Compose into diagram")
    lines.append("    # diagram = m0 >> m1 >> ...")
    
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# MERMAID VISUALIZATION
# ═══════════════════════════════════════════════════════════════════════════════

def to_mermaid(acset: OperadACSet) -> str:
    """Generate Mermaid diagram of operad network."""
    lines = [
        "flowchart TB",
        "    subgraph OperadNetwork[\"DiscoHy Operad Network\"]",
    ]
    
    # Node definitions with trit colors
    trit_colors = {
        Trit.MINUS: "#4444ff",
        Trit.ERGODIC: "#44ff44", 
        Trit.PLUS: "#ff4444",
    }
    
    for key, op in acset.operads.items():
        trit_label = {-1: "⊖", 0: "⊙", 1: "⊕"}[op.trit]
        lines.append(f"        {key}[(\"{op.name}<br/>{trit_label}\")]")
    
    lines.append("    end")
    lines.append("")
    
    # Edges for morphisms
    for m in acset.morphisms:
        arrow = "-->" if m.preserves_gf3 else "-.->|breaks GF3|"
        lines.append(f"    {m.source} {arrow}|{m.morphism_type}| {m.target}")
    
    # Style definitions
    lines.append("")
    lines.append("    classDef minus fill:#4444ff,color:#fff")
    lines.append("    classDef ergodic fill:#44ff44,color:#000")
    lines.append("    classDef plus fill:#ff4444,color:#fff")
    
    for key, op in acset.operads.items():
        class_name = {-1: "minus", 0: "ergodic", 1: "plus"}[op.trit]
        lines.append(f"    class {key} {class_name}")
    
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN: Demo the relational interleaving
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    print("═══ Relational Operad Interleaving via DiscoHy + ACSets ═══\n")
    
    # 1. Build ACSet
    acset = OperadACSet(seed=0x42D)
    print(f"Operad ACSet: {len(acset.operads)} operads, {len(acset.morphisms)} morphisms")
    print(f"GF(3) total: {acset.gf3_total()} (should be 0 for conservation)")
    
    # 2. Build triad interleaving
    triad = build_triad_from_operads()
    schedule = triad.build_round_robin(7)
    print(f"\n─── Triad Schedule ({len(schedule)} triplets) ───")
    for i, (m, e, p) in enumerate(schedule):
        print(f"  {i}: {m:15} ⊗ {e:15} ⊗ {p:15}")
    print(f"GF(3) verified: {triad.verify_gf3()}")
    
    # 3. Compute compositions
    compositions = compute_all_compositions(acset)
    print(f"\n─── Operad Compositions ({len(compositions)}) ───")
    for comp in compositions[:3]:
        print(f"  {comp['source']} →[{comp['morphism_type']}]→ {comp['target']}")
        print(f"    combined_trit={comp['combined_trit']}, gf3_preserved={comp['gf3_preserved']}")
    
    # 4. Success tracking
    tracker = SuccessTracker(acset)
    for key in list(acset.operads.keys())[:3]:
        tracker.log_success(key, 42.0, [f"artifact_{key}.py"])
    
    print(f"\n─── Success Patterns ({len(tracker.patterns)}) ───")
    for p in tracker.patterns:
        print(f"  {p.operad_key}: {p.color_hex} @ {p.execution_time_ms}ms")
    
    # 5. Mermaid output
    print(f"\n─── Mermaid Diagram ───")
    print(to_mermaid(acset))
    
    # 6. DisCoPy code
    print(f"\n─── DisCoPy Code ───")
    print(to_discopy_monoidal(acset)[:500] + "...")


if __name__ == "__main__":
    main()
