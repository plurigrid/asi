#!/usr/bin/env python3
"""
DiscoHy Cubes Operad: Agent 2 Parallel-Fanout Activities

Models Agent 2 skills as cubes in n-dimensional space:
  - xenodium-elisp: Emacs dimension
  - tailscale-file-transfer: Network mesh dimension  
  - parallel-fanout: Concurrency dimension

The E_∞ Cubes operad provides infinite-dimensional parallelism
where configuration spaces of unit cubes in R^∞ model parallel composition.

Extends: discohy_thread_operad.py patterns
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from enum import IntEnum
from typing import Any
from itertools import combinations, product

# SplitMix64 constants from parent
GOLDEN: int = 0x9E3779B97F4A7C15
MIX1: int = 0xBF58476D1CE4E5B9
MIX2: int = 0x94D049BB133111EB
MASK64: int = 0xFFFFFFFFFFFFFFFF


def mix64(z: int) -> int:
    """SplitMix64 mixing function."""
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    return (z ^ (z >> 31)) & MASK64


class TritState(IntEnum):
    """GF(3) states for cube coloring."""
    MINUS = -1   # Backfill / historical
    ZERO = 0     # Verify / ergodic
    PLUS = 1     # Live / forward


# ═══════════════════════════════════════════════════════════════════════════════
# CUBE: Unit hypercube in R^n
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Cube:
    """Unit cube positioned in n-dimensional space.
    
    A cube is defined by its anchor point (min corner) and dimension n.
    Agent 2's skills map to cube dimensions:
      dim 0: xenodium-elisp (Emacs interaction)
      dim 1: tailscale-file-transfer (mesh network)
      dim 2: parallel-fanout (concurrency degree)
      dim 3+: Extended action space
    """
    position: tuple[float, ...]  # Anchor point (min corner)
    seed: int = 0x42D
    label: str = ""
    trit: TritState = TritState.ZERO
    
    @property
    def dimension(self) -> int:
        return len(self.position)
    
    @property
    def corners(self) -> list[tuple[float, ...]]:
        """All 2^n corners of the unit cube."""
        offsets = list(product([0, 1], repeat=self.dimension))
        return [
            tuple(p + o for p, o in zip(self.position, offset))
            for offset in offsets
        ]
    
    @property
    def center(self) -> tuple[float, ...]:
        """Center of the cube."""
        return tuple(p + 0.5 for p in self.position)
    
    def color_from_seed(self) -> dict[str, float]:
        """Deterministic LCH color from seed."""
        h = mix64(self.seed)
        return {
            "L": 25 + ((h >> 48) & 0xFFFF) / 65535 * 50,
            "C": ((h >> 32) & 0xFFFF) / 65535 * 100,
            "H": ((h >> 16) & 0xFFFF) / 65535 * 360,
        }
    
    def faces(self, dim: int) -> tuple["Cube", "Cube"]:
        """Get the two faces perpendicular to dimension dim."""
        lower = list(self.position)
        upper = list(self.position)
        upper[dim] += 1
        
        # Faces are (n-1)-dimensional cubes
        lower_face_pos = tuple(p for i, p in enumerate(lower) if i != dim)
        upper_face_pos = tuple(p for i, p in enumerate(upper) if i != dim)
        
        return (
            Cube(lower_face_pos, seed=self.seed, label=f"{self.label}_d{dim}_lo"),
            Cube(upper_face_pos, seed=self.seed, label=f"{self.label}_d{dim}_hi"),
        )
    
    def to_dict(self) -> dict[str, Any]:
        return {
            "position": self.position,
            "dimension": self.dimension,
            "seed": self.seed,
            "label": self.label,
            "trit": int(self.trit),
            "color": self.color_from_seed(),
            "center": self.center,
        }


# ═══════════════════════════════════════════════════════════════════════════════
# CUBES CONFIGURATION: Agent 2 Skill Space
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class CubesConfiguration:
    """Configuration of non-overlapping unit cubes in R^n.
    
    This models Agent 2's parallel activities:
    - Each cube = one parallel task
    - Non-overlap = tasks execute independently
    - Dimension = skill axes (xenodium, tailscale, parallel-fanout)
    """
    cubes: list[Cube] = field(default_factory=list)
    dimension: int = 3  # Default: Agent 2's 3 skills
    genesis_seed: int = 0x42D
    
    def add_cube(self, position: tuple[float, ...], label: str = "") -> Cube:
        """Add a cube at given position if non-overlapping."""
        seed = int(hashlib.sha256(str(position).encode()).hexdigest(), 16) & MASK64
        trit = TritState(((seed >> 12) % 3) - 1)  # -1, 0, or 1
        
        cube = Cube(position, seed=seed, label=label, trit=trit)
        
        if not self._overlaps(cube):
            self.cubes.append(cube)
            return cube
        raise ValueError(f"Cube at {position} overlaps existing cubes")
    
    def _overlaps(self, new_cube: Cube) -> bool:
        """Check if new cube overlaps any existing cube."""
        for cube in self.cubes:
            if self._cubes_overlap(cube, new_cube):
                return True
        return False
    
    def _cubes_overlap(self, c1: Cube, c2: Cube) -> bool:
        """Check if two unit cubes overlap (interior intersection)."""
        for i in range(min(c1.dimension, c2.dimension)):
            p1, p2 = c1.position[i], c2.position[i]
            # Cubes are unit size, so overlap if distance < 1 in all dims
            if abs(p1 - p2) >= 1:
                return False
        return True
    
    def parallel_degree(self) -> int:
        """Number of parallel activities (cubes) at maximum."""
        return len(self.cubes)
    
    def gf3_conservation(self) -> dict[str, Any]:
        """Check GF(3) conservation for all triplets."""
        if len(self.cubes) < 3:
            return {"conserved": True, "triplets_checked": 0}
        
        violations = []
        triplets = list(combinations(range(len(self.cubes)), 3))
        
        for i, j, k in triplets:
            trit_sum = (
                self.cubes[i].trit + 
                self.cubes[j].trit + 
                self.cubes[k].trit
            )
            if trit_sum % 3 != 0:
                violations.append({
                    "indices": (i, j, k),
                    "labels": (self.cubes[i].label, self.cubes[j].label, self.cubes[k].label),
                    "trit_sum": trit_sum,
                })
        
        return {
            "conserved": len(violations) == 0,
            "triplets_checked": len(triplets),
            "violations": violations,
        }
    
    def to_dict(self) -> dict[str, Any]:
        return {
            "dimension": self.dimension,
            "cube_count": len(self.cubes),
            "genesis_seed": self.genesis_seed,
            "parallel_degree": self.parallel_degree(),
            "gf3_check": self.gf3_conservation(),
            "cubes": [c.to_dict() for c in self.cubes],
        }


# ═══════════════════════════════════════════════════════════════════════════════
# CUBES OPERAD: E_∞ Structure
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass  
class CubesOperad:
    """E_∞ Cubes operad modeling infinite-dimensional parallelism.
    
    Operations: C(n) = configurations of n labeled unit cubes in R^∞
    Composition: ∘_i glues configuration at the i-th cube
    
    For Agent 2:
      C(1) = single skill activation
      C(2) = two parallel skills (xenodium + tailscale)
      C(3) = full triad (xenodium + tailscale + parallel-fanout)
      C(n) = extended parallel fanout with n tasks
    """
    
    configurations: dict[int, list[CubesConfiguration]] = field(default_factory=dict)
    skill_dimensions: dict[str, int] = field(default_factory=lambda: {
        "xenodium-elisp": 0,
        "tailscale-file-transfer": 1,
        "parallel-fanout": 2,
    })
    
    def register_skill(self, skill_name: str) -> int:
        """Register a skill as a new dimension."""
        if skill_name not in self.skill_dimensions:
            new_dim = len(self.skill_dimensions)
            self.skill_dimensions[skill_name] = new_dim
        return self.skill_dimensions[skill_name]
    
    def create_configuration(self, arity: int) -> CubesConfiguration:
        """Create a configuration of `arity` cubes."""
        config = CubesConfiguration(dimension=len(self.skill_dimensions))
        
        if arity not in self.configurations:
            self.configurations[arity] = []
        self.configurations[arity].append(config)
        
        return config
    
    def compose(
        self, 
        outer: CubesConfiguration, 
        inner: CubesConfiguration, 
        port: int
    ) -> CubesConfiguration:
        """Compose configurations: substitute `inner` at cube `port` of `outer`.
        
        This is the E_∞ operad composition:
          (γ; δ_1, ..., δ_n) where γ ∈ C(n) and δ_i ∈ C(k_i)
        """
        if port >= len(outer.cubes):
            raise ValueError(f"Port {port} out of range for configuration with {len(outer.cubes)} cubes")
        
        result = CubesConfiguration(
            dimension=max(outer.dimension, inner.dimension)
        )
        
        # Copy cubes from outer, except at port
        target_cube = outer.cubes[port]
        for i, cube in enumerate(outer.cubes):
            if i != port:
                result.cubes.append(cube)
        
        # Translate inner cubes to target position
        for cube in inner.cubes:
            new_pos = tuple(
                target_cube.position[j] + cube.position[j] 
                for j in range(min(len(target_cube.position), len(cube.position)))
            )
            # Pad with zeros if dimensions differ
            if len(new_pos) < result.dimension:
                new_pos = new_pos + (0.0,) * (result.dimension - len(new_pos))
            
            result.cubes.append(Cube(
                position=new_pos,
                seed=cube.seed,
                label=f"{target_cube.label}_{cube.label}",
                trit=cube.trit,
            ))
        
        return result
    
    def parallel_compose(
        self, 
        configs: list[CubesConfiguration]
    ) -> CubesConfiguration:
        """Parallel (tensor) composition: place all configurations side-by-side.
        
        This is Agent 2's parallel-fanout in action.
        """
        result = CubesConfiguration(
            dimension=max(c.dimension for c in configs) if configs else 3
        )
        
        offset = 0.0
        for i, config in enumerate(configs):
            for cube in config.cubes:
                # Shift along dimension 2 (parallel-fanout axis)
                new_pos = list(cube.position)
                while len(new_pos) < result.dimension:
                    new_pos.append(0.0)
                new_pos[2] += offset  # Shift along fanout axis
                
                result.cubes.append(Cube(
                    position=tuple(new_pos),
                    seed=cube.seed,
                    label=f"par_{i}_{cube.label}",
                    trit=cube.trit,
                ))
            offset += 2.0  # Leave gap between parallel groups
        
        return result
    
    def to_discopy_diagram(self, config: CubesConfiguration) -> dict[str, Any]:
        """Convert configuration to DisCoPy monoidal diagram."""
        boxes = []
        for cube in config.cubes:
            boxes.append({
                "name": cube.label or f"cube_{id(cube)}",
                "dom": [f"in_{i}" for i in range(cube.dimension)],
                "cod": [f"out_{i}" for i in range(cube.dimension)],
                "position": cube.position,
                "color": cube.color_from_seed(),
            })
        
        # Wires connect adjacent cubes along each dimension
        wires = []
        for i, c1 in enumerate(config.cubes):
            for j, c2 in enumerate(config.cubes):
                if i < j:
                    # Check if cubes are adjacent (differ by 1 in exactly one dim)
                    diff = [abs(p1 - p2) for p1, p2 in zip(c1.position, c2.position)]
                    if diff.count(1) == 1 and diff.count(0) == len(diff) - 1:
                        wires.append({
                            "src": c1.label,
                            "tgt": c2.label,
                            "dim": diff.index(1),
                        })
        
        return {
            "type": "cubes_monoidal_diagram",
            "boxes": boxes,
            "wires": wires,
            "dimension": config.dimension,
        }
    
    def to_dict(self) -> dict[str, Any]:
        return {
            "skill_dimensions": self.skill_dimensions,
            "configurations": {
                arity: [c.to_dict() for c in configs]
                for arity, configs in self.configurations.items()
            },
        }


# ═══════════════════════════════════════════════════════════════════════════════
# AGENT 2 ACTIVITY MODELING
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Agent2Activity:
    """Model Agent 2's parallel-fanout activities as cube configurations."""
    
    operad: CubesOperad = field(default_factory=CubesOperad)
    
    def model_skill_activation(
        self, 
        skills: list[str], 
        intensities: list[float] | None = None
    ) -> CubesConfiguration:
        """Model activation of skills as cubes positioned by intensity."""
        if intensities is None:
            intensities = [1.0] * len(skills)
        
        config = self.operad.create_configuration(len(skills))
        
        for skill, intensity in zip(skills, intensities):
            dim = self.operad.register_skill(skill)
            
            # Position cube based on skill dimension and intensity
            pos = [0.0] * config.dimension
            pos[dim % config.dimension] = intensity
            
            config.add_cube(tuple(pos), label=skill)
        
        return config
    
    def model_tailscale_mesh(self, peers: list[str]) -> CubesConfiguration:
        """Model Tailscale mesh topology as hypercube configuration."""
        # Tailscale mesh is naturally a hypercube topology
        n_peers = len(peers)
        dim = max(3, n_peers.bit_length())  # At least 3D for visibility
        
        config = CubesConfiguration(dimension=dim)
        
        # Place peers at hypercube vertices
        for i, peer in enumerate(peers):
            # Binary encoding of index gives position
            pos = tuple(float((i >> d) & 1) for d in range(dim))
            config.add_cube(pos, label=peer)
        
        return config
    
    def model_parallel_fanout(
        self, 
        tasks: list[dict[str, Any]]
    ) -> CubesConfiguration:
        """Model parallel task fanout."""
        task_configs = []
        
        for task in tasks:
            task_config = CubesConfiguration(dimension=3)
            priority = task.get("priority", 0)
            
            # Each task gets a cube, position encodes metadata
            pos = (
                float(task.get("elisp_weight", 0)),
                float(task.get("network_weight", 0)),
                float(priority),
            )
            task_config.add_cube(pos, label=task.get("name", "task"))
            task_configs.append(task_config)
        
        return self.operad.parallel_compose(task_configs)


# ═══════════════════════════════════════════════════════════════════════════════
# DEMO
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    """Demo Agent 2 Cubes Operad."""
    print("═══ DiscoHy Cubes Operad: Agent 2 ═══\n")
    
    agent2 = Agent2Activity()
    
    # Model Agent 2's three core skills
    print("─── Core Skill Activation ───")
    core_skills = agent2.model_skill_activation(
        skills=["xenodium-elisp", "tailscale-file-transfer", "parallel-fanout"],
        intensities=[1.0, 1.5, 2.0]
    )
    print(f"Cubes: {len(core_skills.cubes)}")
    print(f"Parallel degree: {core_skills.parallel_degree()}")
    print(f"GF(3): {core_skills.gf3_conservation()}")
    
    # Model Tailscale mesh
    print("\n─── Tailscale Mesh (Hypercube) ───")
    mesh = agent2.model_tailscale_mesh([
        "mbp-local", "server-nyc", "pi-home", "vm-cloud"
    ])
    print(f"Mesh cubes: {len(mesh.cubes)}")
    print(f"Mesh dimension: {mesh.dimension}")
    
    # Model parallel fanout
    print("\n─── Parallel Fanout ───")
    tasks = [
        {"name": "file-sync", "elisp_weight": 1, "network_weight": 2, "priority": 0},
        {"name": "status-check", "elisp_weight": 0.5, "network_weight": 1, "priority": 1},
        {"name": "deploy-wasm", "elisp_weight": 0, "network_weight": 3, "priority": 2},
    ]
    fanout = agent2.model_parallel_fanout(tasks)
    print(f"Fanout cubes: {len(fanout.cubes)}")
    print(f"GF(3): {fanout.gf3_conservation()}")
    
    # DisCoPy representation
    print("\n─── DisCoPy Diagram ───")
    diagram = agent2.operad.to_discopy_diagram(core_skills)
    print(json.dumps(diagram, indent=2))
    
    # Operad composition example
    print("\n─── Operad Composition ───")
    inner = agent2.model_skill_activation(["sub-task-a", "sub-task-b"])
    composed = agent2.operad.compose(core_skills, inner, port=1)
    print(f"Composed cubes: {len(composed.cubes)}")
    print(f"Labels: {[c.label for c in composed.cubes]}")
    
    # Full summary
    print("\n─── Full Operad Summary ───")
    print(json.dumps(agent2.operad.to_dict(), indent=2, default=str))


if __name__ == "__main__":
    main()
