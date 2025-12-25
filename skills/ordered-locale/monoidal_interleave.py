#!/usr/bin/env python3
"""
monoidal_interleave.py - Monoidal Tensor Product Skill Interleaving

Propagates ordered-locale and glass-hopping awareness to all ASI skills
using monoidal categories, chiral logic, and graphical languages.

When monoidal structure fails, falls back to triadic trifurcation.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Dict, Set, Tuple, Optional, Callable, Any
from enum import Enum
import subprocess
import sys

# ============================================================================
# Chirality and Tensorial Structure
# ============================================================================

class Chirality(Enum):
    """Chiral orientation for monoidal operations"""
    LEFT = -1    # Left adjoint (⊣), contravariant
    NEUTRAL = 0  # Self-adjoint, invariant
    RIGHT = 1    # Right adjoint (⊢), covariant


@dataclass
class Ty:
    """Type in a monoidal category (DisCoPy-style)"""
    name: str
    chirality: Chirality = Chirality.NEUTRAL
    
    def __matmul__(self, other: 'Ty') -> 'TensorTy':
        """Tensor product: A ⊗ B"""
        return TensorTy([self, other])
    
    def __repr__(self):
        chi = {Chirality.LEFT: "ᴸ", Chirality.NEUTRAL: "", Chirality.RIGHT: "ᴿ"}
        return f"{self.name}{chi[self.chirality]}"


@dataclass
class TensorTy:
    """Tensor product of types"""
    factors: List[Ty]
    
    def __matmul__(self, other):
        if isinstance(other, Ty):
            return TensorTy(self.factors + [other])
        elif isinstance(other, TensorTy):
            return TensorTy(self.factors + other.factors)
        raise TypeError(f"Cannot tensor with {type(other)}")
    
    def __repr__(self):
        return " ⊗ ".join(str(t) for t in self.factors)


# ============================================================================
# Skill as Monoidal Box
# ============================================================================

@dataclass
class SkillBox:
    """
    A skill as a box in a monoidal category.
    
    Box: dom → cod with internal structure
    """
    name: str
    dom: TensorTy  # Input types
    cod: TensorTy  # Output types
    trit: int      # GF(3) polarity
    chirality: Chirality = Chirality.NEUTRAL
    depends_on: List[str] = field(default_factory=list)
    aware_of: Set[str] = field(default_factory=set)
    
    def __rshift__(self, other: 'SkillBox') -> 'SkillDiagram':
        """Sequential composition: f >> g"""
        return SkillDiagram([self, other], composition="sequential")
    
    def __matmul__(self, other: 'SkillBox') -> 'SkillDiagram':
        """Parallel composition: f ⊗ g"""
        return SkillDiagram([self, other], composition="parallel")
    
    def make_aware(self, skill_name: str):
        """Add awareness of another skill"""
        self.aware_of.add(skill_name)
    
    def chiral_dual(self) -> 'SkillBox':
        """Return the chiral dual (flip chirality)"""
        new_chi = Chirality(-self.chirality.value) if self.chirality != Chirality.NEUTRAL else Chirality.NEUTRAL
        return SkillBox(
            name=f"{self.name}†",
            dom=self.cod,
            cod=self.dom,
            trit=-self.trit,
            chirality=new_chi,
            depends_on=list(self.depends_on),
            aware_of=set(self.aware_of)
        )


@dataclass
class SkillDiagram:
    """Composition of skill boxes"""
    boxes: List[SkillBox]
    composition: str  # "sequential" or "parallel"
    
    @property
    def trit_sum(self) -> int:
        return sum(b.trit for b in self.boxes)
    
    def is_gf3_conserved(self) -> bool:
        return self.trit_sum % 3 == 0
    
    def __rshift__(self, other):
        if isinstance(other, SkillBox):
            return SkillDiagram(self.boxes + [other], "sequential")
        elif isinstance(other, SkillDiagram):
            return SkillDiagram(self.boxes + other.boxes, "sequential")
        raise TypeError()
    
    def __matmul__(self, other):
        if isinstance(other, SkillBox):
            return SkillDiagram(self.boxes + [other], "parallel")
        elif isinstance(other, SkillDiagram):
            return SkillDiagram(self.boxes + other.boxes, "parallel")
        raise TypeError()


# ============================================================================
# ASI Skill Network
# ============================================================================

# Core skill types
FRAME = Ty("Frame", Chirality.NEUTRAL)
OPEN = Ty("Open", Chirality.NEUTRAL)
BRIDGE = Ty("Bridge", Chirality.RIGHT)  # Covariant (forward-directed)
BEAD = Ty("Bead", Chirality.NEUTRAL)
WORLD = Ty("World", Chirality.NEUTRAL)
SHEAF = Ty("Sheaf", Chirality.LEFT)     # Contravariant (restriction)
TRIT = Ty("Trit", Chirality.NEUTRAL)

# New skills to propagate
ORDERED_LOCALE = SkillBox(
    name="ordered-locale",
    dom=TensorTy([FRAME]),
    cod=TensorTy([OPEN, BRIDGE]),
    trit=0,
    chirality=Chirality.NEUTRAL,
    depends_on=["sheaf-cohomology", "directed-interval"],
    aware_of=set()
)

GLASS_HOPPING = SkillBox(
    name="glass-hopping",
    dom=TensorTy([BEAD, WORLD]),
    cod=TensorTy([WORLD, BRIDGE]),
    trit=0,
    chirality=Chirality.NEUTRAL,
    depends_on=["glass-bead-game", "world-hopping", "ordered-locale"],
    aware_of={"ordered-locale"}
)

# Existing ASI skills
ASI_SKILLS = {
    "acsets": SkillBox("acsets", TensorTy([FRAME]), TensorTy([FRAME]), -1, Chirality.LEFT),
    "gay-mcp": SkillBox("gay-mcp", TensorTy([TRIT]), TensorTy([TRIT, TRIT, TRIT]), +1, Chirality.RIGHT),
    "bisimulation-game": SkillBox("bisimulation-game", TensorTy([WORLD, WORLD]), TensorTy([TRIT]), -1, Chirality.NEUTRAL),
    "world-hopping": SkillBox("world-hopping", TensorTy([WORLD]), TensorTy([WORLD]), -1, Chirality.RIGHT),
    "glass-bead-game": SkillBox("glass-bead-game", TensorTy([BEAD, BEAD]), TensorTy([BEAD]), +1, Chirality.NEUTRAL),
    "triad-interleave": SkillBox("triad-interleave", TensorTy([TRIT, TRIT, TRIT]), TensorTy([TRIT]), +1, Chirality.NEUTRAL),
    "unworld": SkillBox("unworld", TensorTy([WORLD]), TensorTy([WORLD]), 0, Chirality.NEUTRAL),
    "parallel-fanout": SkillBox("parallel-fanout", TensorTy([TRIT]), TensorTy([TRIT, TRIT, TRIT]), 0, Chirality.NEUTRAL),
    "sheaf-cohomology": SkillBox("sheaf-cohomology", TensorTy([SHEAF]), TensorTy([TRIT]), -1, Chirality.LEFT),
    "directed-interval": SkillBox("directed-interval", TensorTy([OPEN]), TensorTy([BRIDGE]), 0, Chirality.RIGHT),
    "discopy": SkillBox("discopy", TensorTy([BEAD]), TensorTy([BEAD]), 0, Chirality.NEUTRAL),
}


# ============================================================================
# Monoidal Interleaving
# ============================================================================

class MonoidalInterleaver:
    """
    Interleaves new skills into the ASI network using monoidal tensor product.
    
    Strategy:
    1. Find compatible type interfaces (dom/cod matching)
    2. Tensor new skills with existing ones
    3. Verify GF(3) conservation
    4. Propagate awareness bidirectionally
    5. Fall back to trifurcation on failure
    """
    
    def __init__(self, skills: Dict[str, SkillBox]):
        self.skills = dict(skills)
        self.diagrams: List[SkillDiagram] = []
        self.failures: List[Tuple[str, str, str]] = []
    
    def type_compatible(self, s1: SkillBox, s2: SkillBox) -> bool:
        """Check if s1.cod can connect to s2.dom"""
        # Simplified: check if any type in cod appears in dom
        cod_types = {t.name for t in s1.cod.factors}
        dom_types = {t.name for t in s2.dom.factors}
        return bool(cod_types & dom_types)
    
    def chirality_compatible(self, s1: SkillBox, s2: SkillBox) -> bool:
        """Check chiral compatibility for composition"""
        if s1.chirality == Chirality.NEUTRAL or s2.chirality == Chirality.NEUTRAL:
            return True
        if s1.chirality == Chirality.RIGHT and s2.chirality == Chirality.LEFT:
            return True  # Adjunction pair
        return s1.chirality == s2.chirality
    
    def try_sequential(self, s1: SkillBox, s2: SkillBox) -> Optional[SkillDiagram]:
        """Try sequential composition: s1 >> s2"""
        if not self.type_compatible(s1, s2):
            return None
        if not self.chirality_compatible(s1, s2):
            return None
        
        diagram = s1 >> s2
        if diagram.is_gf3_conserved():
            return diagram
        return None
    
    def try_parallel(self, s1: SkillBox, s2: SkillBox) -> Optional[SkillDiagram]:
        """Try parallel composition: s1 ⊗ s2"""
        diagram = s1 @ s2
        # Parallel always works but may not conserve GF(3)
        return diagram if diagram.is_gf3_conserved() else None
    
    def try_tensor_with_third(
        self, 
        s1: SkillBox, 
        s2: SkillBox, 
        gf3_target: int = 0
    ) -> Optional[SkillDiagram]:
        """Find a third skill to make GF(3) = 0"""
        needed_trit = -(s1.trit + s2.trit) % 3
        if needed_trit == 2:
            needed_trit = -1
        
        for name, skill in self.skills.items():
            if skill.trit == needed_trit:
                diagram = s1 @ s2 @ skill
                if diagram.is_gf3_conserved():
                    return diagram
        return None
    
    def trifurcate_fallback(
        self, 
        new_skill: SkillBox,
        context: str
    ) -> List[SkillDiagram]:
        """
        Fallback: trifurcate into 3 parallel attempts.
        
        MINUS: Validate compatibility
        ERGODIC: Coordinate awareness
        PLUS: Generate connections
        """
        results = []
        
        # MINUS: Try with contravariant (LEFT) skills
        left_skills = [s for s in self.skills.values() if s.chirality == Chirality.LEFT]
        for ls in left_skills[:3]:
            diagram = ls @ new_skill
            results.append(diagram)
            self.propagate_awareness(ls, new_skill)
        
        # ERGODIC: Try with neutral skills
        neutral_skills = [s for s in self.skills.values() if s.chirality == Chirality.NEUTRAL]
        for ns in neutral_skills[:3]:
            diagram = ns @ new_skill
            results.append(diagram)
            self.propagate_awareness(ns, new_skill)
        
        # PLUS: Try with covariant (RIGHT) skills
        right_skills = [s for s in self.skills.values() if s.chirality == Chirality.RIGHT]
        for rs in right_skills[:3]:
            diagram = new_skill @ rs
            results.append(diagram)
            self.propagate_awareness(new_skill, rs)
        
        return results
    
    def propagate_awareness(self, s1: SkillBox, s2: SkillBox):
        """Bidirectional awareness propagation"""
        s1.make_aware(s2.name)
        s2.make_aware(s1.name)
    
    def interleave_skill(self, new_skill: SkillBox) -> Dict[str, Any]:
        """
        Main entry point: interleave a new skill into the network.
        
        Returns report of connections made.
        """
        report = {
            "skill": new_skill.name,
            "sequential": [],
            "parallel": [],
            "triadic": [],
            "fallback": [],
            "gf3_conserved": True
        }
        
        for name, existing in self.skills.items():
            # Try sequential: existing >> new
            seq = self.try_sequential(existing, new_skill)
            if seq:
                self.diagrams.append(seq)
                report["sequential"].append((existing.name, new_skill.name))
                self.propagate_awareness(existing, new_skill)
                continue
            
            # Try sequential: new >> existing
            seq_rev = self.try_sequential(new_skill, existing)
            if seq_rev:
                self.diagrams.append(seq_rev)
                report["sequential"].append((new_skill.name, existing.name))
                self.propagate_awareness(new_skill, existing)
                continue
            
            # Try parallel
            par = self.try_parallel(existing, new_skill)
            if par:
                self.diagrams.append(par)
                report["parallel"].append((existing.name, new_skill.name))
                self.propagate_awareness(existing, new_skill)
                continue
            
            # Try tensor with third (GF(3) balancing)
            tri = self.try_tensor_with_third(existing, new_skill)
            if tri:
                self.diagrams.append(tri)
                report["triadic"].append(tuple(b.name for b in tri.boxes))
                for b in tri.boxes:
                    self.propagate_awareness(b, new_skill)
                continue
            
            # Record failure for fallback
            self.failures.append((existing.name, new_skill.name, "no compatible composition"))
        
        # Fallback trifurcation for failures
        if self.failures:
            fallback_diagrams = self.trifurcate_fallback(new_skill, "monoidal failure")
            report["fallback"] = [tuple(b.name for b in d.boxes) for d in fallback_diagrams]
            self.diagrams.extend(fallback_diagrams)
        
        # Add to skill network
        self.skills[new_skill.name] = new_skill
        
        # Final GF(3) check
        total_trit = sum(s.trit for s in self.skills.values())
        report["gf3_conserved"] = total_trit % 3 == 0
        report["total_diagrams"] = len(self.diagrams)
        
        return report
    
    def generate_awareness_updates(self) -> Dict[str, Set[str]]:
        """Generate awareness map for all skills"""
        return {name: skill.aware_of for name, skill in self.skills.items()}


# ============================================================================
# Graphical Language Output
# ============================================================================

def to_discopy_diagram(diagram: SkillDiagram) -> str:
    """Generate DisCoPy code for the diagram"""
    lines = [
        "from discopy.monoidal import Ty, Box, Diagram",
        "",
        "# Types",
    ]
    
    # Collect all types
    all_types = set()
    for box in diagram.boxes:
        for t in box.dom.factors:
            all_types.add(t.name)
        for t in box.cod.factors:
            all_types.add(t.name)
    
    for ty in sorted(all_types):
        lines.append(f"{ty.lower()} = Ty('{ty}')")
    
    lines.append("")
    lines.append("# Boxes")
    
    for box in diagram.boxes:
        dom_str = " @ ".join(t.name.lower() for t in box.dom.factors)
        cod_str = " @ ".join(t.name.lower() for t in box.cod.factors)
        lines.append(f"{box.name.replace('-', '_')} = Box('{box.name}', {dom_str}, {cod_str})")
    
    lines.append("")
    lines.append("# Composition")
    
    if diagram.composition == "sequential":
        comp_str = " >> ".join(b.name.replace('-', '_') for b in diagram.boxes)
    else:
        comp_str = " @ ".join(b.name.replace('-', '_') for b in diagram.boxes)
    
    lines.append(f"diagram = {comp_str}")
    lines.append("diagram.draw()")
    
    return "\n".join(lines)


def to_mermaid(diagram: SkillDiagram) -> str:
    """Generate Mermaid diagram code"""
    lines = ["graph LR"]
    
    for i, box in enumerate(diagram.boxes):
        chi_sym = {Chirality.LEFT: "⊣", Chirality.NEUTRAL: "○", Chirality.RIGHT: "⊢"}
        trit_sym = {-1: "-", 0: "0", 1: "+"}
        label = f"{box.name}<br/>{chi_sym[box.chirality]} trit={trit_sym[box.trit]}"
        lines.append(f"    B{i}[\"{label}\"]")
    
    if diagram.composition == "sequential":
        for i in range(len(diagram.boxes) - 1):
            lines.append(f"    B{i} --> B{i+1}")
    else:
        # Parallel: connect to common source/sink
        lines.append("    SRC((⊗)) --> B0")
        for i in range(1, len(diagram.boxes)):
            lines.append(f"    SRC --> B{i}")
        for i in range(len(diagram.boxes)):
            lines.append(f"    B{i} --> SNK((⊗))")
    
    return "\n".join(lines)


# ============================================================================
# CLI
# ============================================================================

def main():
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║  MONOIDAL SKILL INTERLEAVING                                  ║")
    print("║  Tensor product propagation with chiral logic                 ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    
    # Initialize interleaver with existing skills
    interleaver = MonoidalInterleaver(ASI_SKILLS)
    
    # Interleave ordered-locale
    print("\n─── Interleaving: ordered-locale ───")
    report1 = interleaver.interleave_skill(ORDERED_LOCALE)
    print(f"  Sequential: {len(report1['sequential'])}")
    print(f"  Parallel: {len(report1['parallel'])}")
    print(f"  Triadic: {len(report1['triadic'])}")
    print(f"  Fallback: {len(report1['fallback'])}")
    
    # Interleave glass-hopping
    print("\n─── Interleaving: glass-hopping ───")
    report2 = interleaver.interleave_skill(GLASS_HOPPING)
    print(f"  Sequential: {len(report2['sequential'])}")
    print(f"  Parallel: {len(report2['parallel'])}")
    print(f"  Triadic: {len(report2['triadic'])}")
    print(f"  Fallback: {len(report2['fallback'])}")
    
    # Awareness map
    print("\n─── Awareness Propagation ───")
    awareness = interleaver.generate_awareness_updates()
    for skill, aware_of in sorted(awareness.items()):
        if aware_of:
            print(f"  {skill}: aware of {aware_of}")
    
    # GF(3) verification
    print("\n─── GF(3) Conservation ───")
    total = sum(s.trit for s in interleaver.skills.values())
    print(f"  Total trit sum: {total}")
    print(f"  Conserved: {'✓' if total % 3 == 0 else '✗'}")
    
    # Sample DisCoPy output
    if interleaver.diagrams:
        print("\n─── Sample DisCoPy Diagram ───")
        sample = interleaver.diagrams[0]
        print(to_discopy_diagram(sample))
    
    print("\n" + "═" * 60)
    print(f"  Total diagrams created: {len(interleaver.diagrams)}")
    print(f"  Skills now aware of new skills: {len(awareness)}")
    print("═" * 60)


if __name__ == "__main__":
    main()
