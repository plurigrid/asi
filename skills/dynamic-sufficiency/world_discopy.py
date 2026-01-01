"""
world_discopy.py - Dynamic Sufficiency as DisCoPy Categorical Diagrams

Expresses the world-memory skill system as string diagrams:
- Skills as objects (types)
- Actions as morphisms (boxes)
- GF(3) as a grading on types
- Sufficiency as a functor preserving the grading

The three streams:
  MINUS  (-1): Validators (sufficiency, cohomology, lint)
  ERGODIC (0): Coordinators (dispatch, routing, bridging)
  PLUS   (+1): Generators (install, create, fanout)

GF(3) Conservation: sum(trits) ≡ 0 (mod 3) per triplet
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import List, Dict, Tuple, Any
from functools import reduce


# ════════════════════════════════════════════════════════════════════════════
# Simplified DisCoPy-like Types (no external dependency)
# ════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Ty:
    """A type (object in the category)."""
    name: str
    trit: int = 0  # GF(3) grading
    
    def __add__(self, other: 'Ty') -> 'ProductTy':
        """Tensor product of types."""
        return ProductTy([self, other])
    
    def __repr__(self):
        trit_symbol = {-1: "⊖", 0: "⊙", 1: "⊕"}.get(self.trit, "?")
        return f"{self.name}{trit_symbol}"


@dataclass
class ProductTy:
    """Product (tensor) of types."""
    factors: List[Ty]
    
    @property
    def trit(self) -> int:
        return sum(t.trit for t in self.factors) % 3
    
    def __add__(self, other):
        if isinstance(other, Ty):
            return ProductTy(self.factors + [other])
        elif isinstance(other, ProductTy):
            return ProductTy(self.factors + other.factors)
        return NotImplemented
    
    def __repr__(self):
        return " ⊗ ".join(repr(t) for t in self.factors)


@dataclass
class Box:
    """A morphism (box in the diagram)."""
    name: str
    dom: Ty | ProductTy  # Domain (input type)
    cod: Ty | ProductTy  # Codomain (output type)
    
    def __rshift__(self, other: 'Box') -> 'Compose':
        """Sequential composition: self >> other."""
        return Compose([self, other])
    
    def __matmul__(self, other: 'Box') -> 'Tensor':
        """Parallel composition: self @ other."""
        return Tensor([self, other])
    
    def __repr__(self):
        return f"[{self.name}: {self.dom} → {self.cod}]"


@dataclass
class Compose:
    """Sequential composition of boxes."""
    boxes: List[Box]
    
    @property
    def dom(self):
        return self.boxes[0].dom
    
    @property
    def cod(self):
        return self.boxes[-1].cod
    
    def __rshift__(self, other: Box) -> 'Compose':
        return Compose(self.boxes + [other])
    
    def __repr__(self):
        return " >> ".join(repr(b) for b in self.boxes)


@dataclass
class Tensor:
    """Parallel composition of boxes."""
    boxes: List[Box]
    
    def __matmul__(self, other: Box) -> 'Tensor':
        return Tensor(self.boxes + [other])
    
    @property
    def trit_sum(self) -> int:
        """Sum of trits of output types."""
        total = 0
        for b in self.boxes:
            if isinstance(b.cod, Ty):
                total += b.cod.trit
            elif isinstance(b.cod, ProductTy):
                total += b.cod.trit
        return total % 3
    
    def __repr__(self):
        return " ⊗ ".join(repr(b) for b in self.boxes)


# ════════════════════════════════════════════════════════════════════════════
# GF(3) Graded Types for Skills
# ════════════════════════════════════════════════════════════════════════════

# Base types for each trit
Minus = Ty("−", -1)
Ergodic = Ty("0", 0)
Plus = Ty("+", 1)

# Skill types with their trit grading
SKILL_TYPES = {
    # MINUS (-1): Validators
    "dynamic-sufficiency": Ty("sufficiency", -1),
    "sheaf-cohomology": Ty("cohomology", -1),
    "three-match": Ty("three-match", -1),
    "clj-kondo-3color": Ty("kondo", -1),
    "spi-parallel-verify": Ty("spi-verify", -1),
    "temporal-coalgebra": Ty("coalgebra", -1),
    
    # ERGODIC (0): Coordinators
    "skill-dispatch": Ty("dispatch", 0),
    "unworld": Ty("unworld", 0),
    "acsets": Ty("acsets", 0),
    "cognitive-surrogate": Ty("surrogate", 0),
    "self-evolving-agent": Ty("self-evolve", 0),
    "babashka": Ty("bb", 0),
    
    # PLUS (+1): Generators
    "skill-installer": Ty("installer", 1),
    "gay-mcp": Ty("gay-mcp", 1),
    "triad-interleave": Ty("interleave", 1),
    "agent-o-rama": Ty("agent-o", 1),
    "godel-machine": Ty("godel", 1),
    "mcp-builder": Ty("mcp-build", 1),
}

# Task and Result types
Task = Ty("Task", 0)
CausalState = Ty("CausalState", 0)
Coverage = Ty("Coverage", 0)
Verdict = Ty("Verdict", 0)
WorldModel = Ty("WorldModel", 0)
Gadget = Ty("Gadget", 0)
Result = Ty("Result", 0)


# ════════════════════════════════════════════════════════════════════════════
# Morphisms (Boxes) - The Operations
# ════════════════════════════════════════════════════════════════════════════

# Validation morphisms (-1 stream)
infer_state = Box("infer_state", Task, CausalState)
compute_coverage = Box("coverage", CausalState + SKILL_TYPES["dynamic-sufficiency"], Coverage)
pre_action_gate = Box("gate", Coverage, Verdict)

# Coordination morphisms (0 stream)
dispatch_to_triad = Box("dispatch", Task, Minus + Ergodic + Plus)
route_to_bundle = Box("route", Task, SKILL_TYPES["skill-dispatch"])

# Generation morphisms (+1 stream)
load_skill = Box("load", SKILL_TYPES["skill-installer"], SKILL_TYPES["dynamic-sufficiency"])
fanout = Box("fanout", Task, Gadget + Gadget + Gadget)
merge = Box("merge", Gadget + Gadget + Gadget, Result)


# ════════════════════════════════════════════════════════════════════════════
# Triad Building
# ════════════════════════════════════════════════════════════════════════════

def build_triad(minus_skill: str, ergodic_skill: str, plus_skill: str) -> Dict:
    """Build a GF(3) conserving triad diagram."""
    minus_ty = SKILL_TYPES.get(minus_skill, Ty(minus_skill, -1))
    ergodic_ty = SKILL_TYPES.get(ergodic_skill, Ty(ergodic_skill, 0))
    plus_ty = SKILL_TYPES.get(plus_skill, Ty(plus_skill, 1))
    
    minus_box = Box(f"validate:{minus_skill}", Task, minus_ty)
    ergodic_box = Box(f"coordinate:{ergodic_skill}", Task, ergodic_ty)
    plus_box = Box(f"generate:{plus_skill}", Task, plus_ty)
    
    # Tensor product (parallel)
    tensor = minus_box @ ergodic_box @ plus_box
    
    return {
        "diagram": tensor,
        "skills": [minus_skill, ergodic_skill, plus_skill],
        "types": [minus_ty, ergodic_ty, plus_ty],
        "trits": [-1, 0, 1],
        "gf3_sum": 0,
        "conserved": True,
    }


# Canonical triads
TRIADS = {
    "sufficiency": build_triad("dynamic-sufficiency", "skill-dispatch", "skill-installer"),
    "core": build_triad("three-match", "unworld", "gay-mcp"),
    "database": build_triad("clj-kondo-3color", "acsets", "gay-mcp"),
    "learning": build_triad("spi-parallel-verify", "cognitive-surrogate", "agent-o-rama"),
    "evolution": build_triad("temporal-coalgebra", "self-evolving-agent", "godel-machine"),
}


# ════════════════════════════════════════════════════════════════════════════
# World Operad (Categorical Structure)
# ════════════════════════════════════════════════════════════════════════════

class WorldOperad:
    """
    World memory as an operad algebra.
    
    Operations:
    - compose: Chain skills in sequence (>>)
    - tensor: Run skills in parallel (@)
    - oapply: Apply operad composition rule
    """
    
    def __init__(self, seed: int = 0x42D):
        self.seed = seed
        self.skills: Dict[str, Dict] = {}
        self.observations: List[Dict] = []
        self.complexity = 0.0
    
    def load(self, skill_name: str) -> 'WorldOperad':
        """Load a skill into the operad."""
        if skill_name in SKILL_TYPES:
            ty = SKILL_TYPES[skill_name]
            self.skills[skill_name] = {
                "name": skill_name,
                "type": ty,
                "trit": ty.trit,
                "box": Box(skill_name, Task, ty),
            }
        return self
    
    def compose(self, *skill_names: str) -> Compose:
        """Sequential composition: skill1 >> skill2 >> ..."""
        boxes = [self.skills[name]["box"] for name in skill_names]
        return reduce(lambda a, b: a >> b, boxes)
    
    def tensor(self, *skill_names: str) -> Tensor:
        """Parallel composition: skill1 ⊗ skill2 ⊗ ..."""
        boxes = [self.skills[name]["box"] for name in skill_names]
        return reduce(lambda a, b: a @ b, boxes)
    
    def oapply(self, triad_name: str, inputs: List[str]) -> Dict:
        """Operad algebra evaluation (colimit computation)."""
        triad = TRIADS[triad_name]
        return {
            "triad": triad_name,
            "skills": triad["skills"],
            "inputs": inputs,
            "gf3": triad["gf3_sum"],
            "colimit": Box("oapply", 
                          reduce(lambda a, b: a + b, [Task] * len(inputs)),
                          Result),
        }
    
    def observe(self, skill_name: str, success: bool) -> 'WorldOperad':
        """Record observation for world model update."""
        self.observations.append({"skill": skill_name, "success": success})
        
        # Update complexity (entropy estimate)
        n = len(self.observations)
        successes = sum(1 for o in self.observations if o["success"])
        if n > 0:
            p = successes / n
            if 0 < p < 1:
                from math import log2
                self.complexity = -(p * log2(p) + (1-p) * log2(1-p))
        
        return self
    
    def gf3_check(self, *skill_names: str) -> Dict:
        """Verify GF(3) conservation for skill set."""
        trits = [self.skills[name]["trit"] for name in skill_names]
        total = sum(trits) % 3
        return {
            "skills": skill_names,
            "trits": trits,
            "sum": total,
            "conserved": total == 0,
        }


# ════════════════════════════════════════════════════════════════════════════
# Stream Interleaving
# ════════════════════════════════════════════════════════════════════════════

def interleave_streams(
    minus_stream: List[Any],
    ergodic_stream: List[Any],
    plus_stream: List[Any],
    n_triplets: int
) -> List[Dict]:
    """
    Interleave three streams maintaining GF(3) per triplet.
    
    Output: [−, 0, +, −, 0, +, −, 0, +, ...]
    """
    schedule = []
    for i in range(n_triplets):
        schedule.append({"triplet": i, "trit": -1, "stream": "minus", 
                        "value": minus_stream[i] if i < len(minus_stream) else None})
        schedule.append({"triplet": i, "trit": 0, "stream": "ergodic",
                        "value": ergodic_stream[i] if i < len(ergodic_stream) else None})
        schedule.append({"triplet": i, "trit": 1, "stream": "plus",
                        "value": plus_stream[i] if i < len(plus_stream) else None})
    return schedule


# ════════════════════════════════════════════════════════════════════════════
# Visualization
# ════════════════════════════════════════════════════════════════════════════

def draw_triad_ascii(triad: Dict) -> str:
    """Draw ASCII representation of a triad diagram."""
    skills = triad["skills"]
    trits = triad["trits"]
    
    lines = []
    lines.append("          ┌─────────────────────────────────────┐")
    lines.append("          │              TASK                   │")
    lines.append("          └───────────┬─────────────────────────┘")
    lines.append("                      │")
    lines.append("      ┌───────────────┼───────────────┐")
    lines.append("      │               │               │")
    lines.append("      ▼               ▼               ▼")
    lines.append(f" ┌─────────┐   ┌─────────┐   ┌─────────┐")
    lines.append(f" │ {skills[0][:7]:^7} │   │ {skills[1][:7]:^7} │   │ {skills[2][:7]:^7} │")
    lines.append(f" │  {trits[0]:+d}      │   │   {trits[1]:+d}     │   │   {trits[2]:+d}     │")
    lines.append(f" └────┬────┘   └────┬────┘   └────┬────┘")
    lines.append("      │               │               │")
    lines.append("      └───────────────┼───────────────┘")
    lines.append("                      │")
    lines.append("               GF(3) = 0 ✓")
    
    return "\n".join(lines)


# ════════════════════════════════════════════════════════════════════════════
# CLI / Demo
# ════════════════════════════════════════════════════════════════════════════

def demo():
    print("╔═══════════════════════════════════════════════════════════════════╗")
    print("║  DYNAMIC SUFFICIENCY AS CATEGORICAL DIAGRAMS (DisCoPy)           ║")
    print("╚═══════════════════════════════════════════════════════════════════╝")
    print()
    
    # Create world operad
    world = WorldOperad(0x42D)
    
    # Load skills
    for skill_name in ["dynamic-sufficiency", "skill-dispatch", "skill-installer",
                       "three-match", "unworld", "gay-mcp"]:
        world.load(skill_name)
    
    print("─── Loaded Skills (as Types) ───")
    for name, skill in world.skills.items():
        print(f"  {skill['type']}")
    
    print()
    print("─── GF(3) Verification ───")
    check1 = world.gf3_check("dynamic-sufficiency", "skill-dispatch", "skill-installer")
    symbol1 = "✓" if check1["conserved"] else "✗"
    print(f"  Sufficiency triad: {check1['trits']} → sum={check1['sum']} {symbol1}")
    
    check2 = world.gf3_check("three-match", "unworld", "gay-mcp")
    symbol2 = "✓" if check2["conserved"] else "✗"
    print(f"  Core triad: {check2['trits']} → sum={check2['sum']} {symbol2}")
    
    print()
    print("─── Sequential Composition (>>) ───")
    compose = world.compose("dynamic-sufficiency", "skill-dispatch", "skill-installer")
    print(f"  {compose}")
    
    print()
    print("─── Parallel Composition (⊗) ───")
    tensor = world.tensor("three-match", "unworld", "gay-mcp")
    print(f"  {tensor}")
    print(f"  GF(3) = {tensor.trit_sum}")
    
    print()
    print("─── Triad Diagram (ASCII) ───")
    print(draw_triad_ascii(TRIADS["sufficiency"]))
    
    print()
    print("─── Operad Application (oapply) ───")
    result = world.oapply("core", ["task1", "task2", "task3"])
    print(f"  oapply({result['triad']}, {len(result['inputs'])} inputs)")
    print(f"  Skills: {result['skills']}")
    print(f"  GF(3) = {result['gf3']} ✓")
    
    print()
    print("─── Stream Interleaving ───")
    schedule = interleave_streams(
        ["validate1", "validate2", "validate3"],
        ["coordinate1", "coordinate2", "coordinate3"],
        ["generate1", "generate2", "generate3"],
        3
    )
    for entry in schedule:
        print(f"  Triplet {entry['triplet']}: trit={entry['trit']:+d} "
              f"stream={entry['stream']:8} value={entry['value']}")
    
    print()
    print("─── Observations & Complexity ───")
    world.observe("dynamic-sufficiency", True)
    world.observe("skill-dispatch", True)
    world.observe("skill-installer", True)
    world.observe("gay-mcp", False)
    print(f"  Observations: {len(world.observations)}")
    print(f"  Statistical complexity: {world.complexity:.3f} bits")


if __name__ == "__main__":
    demo()
