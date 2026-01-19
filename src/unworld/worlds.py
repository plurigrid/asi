"""
26 Worlds Integration: Unworld ↔ Vibesnipe Goblins

Maps unworld derivation chains to the 26-world distributed comonad system.
Each goblin in vibesnipe has a GF(3) trit, and unworld patterns route
through worlds based on their trit structure.

Architecture:
    Unworld (derivation) → ThreeMatch (trit pattern) → World routing → Goblin execution

GF(3) World Classification:
    PLUS (+1):  Synthesis/Generation worlds (10 worlds)
    ERGODIC (0): Coordination/Balance worlds (9 worlds)  
    MINUS (-1): Analysis/Verification worlds (7 worlds)
"""

from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional

from .three_match import ThreeMatch
from .chain import UnworldChain


# 26 Worlds with GF(3) trit assignments (from DISTRIBUTED_COMONAD_26_WORLDS.md)
WORLDS_26: Dict[str, int] = {
    # PLUS (+1): Synthesis/Generation - 10 worlds
    "a": 1, "d": 1, "f": 1, "h": 1, "j": 1,
    "m": 1, "p": 1, "u": 1, "w": 1, "y": 1,
    
    # ERGODIC (0): Coordination/Balance - 9 worlds
    "e": 0, "g": 0, "i": 0, "n": 0, "o": 0,
    "r": 0, "s": 0, "x": 0, "z": 0,
    
    # MINUS (-1): Analysis/Verification - 7 worlds
    "b": -1, "c": -1, "k": -1, "l": -1,
    "q": -1, "t": -1, "v": -1,
}

# Inverse mapping: trit → worlds
TRIT_TO_WORLDS: Dict[int, List[str]] = {
    1: [w for w, t in WORLDS_26.items() if t == 1],   # PLUS
    0: [w for w, t in WORLDS_26.items() if t == 0],   # ERGODIC
    -1: [w for w, t in WORLDS_26.items() if t == -1], # MINUS
}


@dataclass
class WorldRoute:
    """
    A route through the 26 worlds based on a ThreeMatch.
    
    Each color in the three-match maps to a world based on its trit.
    """
    pattern: ThreeMatch
    worlds: Tuple[str, str, str]
    trits: Tuple[int, int, int]
    
    @classmethod
    def from_pattern(cls, pattern: ThreeMatch, seed: int = 0) -> "WorldRoute":
        """
        Create a world route from a three-match pattern.
        
        Uses the pattern's trits to select worlds, with the seed
        providing deterministic world selection within each trit class.
        """
        worlds = []
        for i, trit in enumerate(pattern.trits):
            candidates = TRIT_TO_WORLDS[trit]
            # Deterministic selection based on seed and index
            idx = (seed + pattern.depth * 3 + i) % len(candidates)
            worlds.append(candidates[idx])
        
        return cls(
            pattern=pattern,
            worlds=tuple(worlds),
            trits=tuple(pattern.trits),
        )
    
    def is_balanced(self) -> bool:
        """Check if the route is GF(3) balanced."""
        return sum(self.trits) % 3 == 0
    
    def to_nats_subjects(self) -> List[str]:
        """
        Convert to NATS channel subjects.
        
        Forward: ies.a.{world}.state
        Backward: ies.b.{world}.state
        """
        return [f"ies.a.{w}.state" for w in self.worlds]
    
    def __repr__(self) -> str:
        trit_sym = {-1: "−", 0: "○", 1: "+"}
        trits_str = "".join(trit_sym[t] for t in self.trits)
        return f"WorldRoute({self.worlds}, trits=[{trits_str}])"


@dataclass
class WorldChain:
    """
    A chain of world routes derived from an UnworldChain.
    
    This bridges unworld (derivation) with the 26-world distributed comonad.
    """
    genesis_seed: int
    routes: List[WorldRoute]
    
    @classmethod
    def from_unworld(cls, chain: UnworldChain) -> "WorldChain":
        """Create a world chain from an unworld chain."""
        routes = [
            WorldRoute.from_pattern(pattern, chain.genesis_seed)
            for pattern in chain.patterns
        ]
        return cls(genesis_seed=chain.genesis_seed, routes=routes)
    
    def verify_balance(self) -> bool:
        """Verify all routes are GF(3) balanced."""
        return all(r.is_balanced() for r in self.routes)
    
    def world_distribution(self) -> Dict[str, int]:
        """Count how many times each world is visited."""
        counts = {w: 0 for w in WORLDS_26}
        for route in self.routes:
            for world in route.worlds:
                counts[world] += 1
        return counts
    
    def trit_distribution(self) -> Dict[int, int]:
        """Count trit occurrences across all routes."""
        counts = {-1: 0, 0: 0, 1: 0}
        for route in self.routes:
            for trit in route.trits:
                counts[trit] += 1
        return counts
    
    def to_session_contexts(self) -> List[Dict]:
        """
        Convert to session contexts for the 26-world system.
        
        These can be published to NATS channels for distributed execution.
        """
        contexts = []
        for i, route in enumerate(self.routes):
            ctx = {
                "session_id": f"{hex(self.genesis_seed)}-{i}",
                "source_world": route.worlds[0],
                "target_world": route.worlds[-1],
                "via_world": route.worlds[1],
                "pattern": route.pattern.to_dict(),
                "depth": route.pattern.depth,
                "subjects": route.to_nats_subjects(),
            }
            contexts.append(ctx)
        return contexts
    
    def __len__(self) -> int:
        return len(self.routes)
    
    def __getitem__(self, idx: int) -> WorldRoute:
        return self.routes[idx]
    
    def __repr__(self) -> str:
        return f"WorldChain(seed={hex(self.genesis_seed)}, routes={len(self.routes)})"


def derive_world_chain(genesis_seed: int, depth: int) -> WorldChain:
    """
    Derive a world chain directly from seed and depth.
    
    Combines unworld derivation with world routing in one step.
    """
    chain = UnworldChain(genesis_seed=genesis_seed)
    chain.derive(depth, verify_gf3=True)
    return WorldChain.from_unworld(chain)


def find_balanced_quad(seed: int, start_depth: int = 0) -> Optional[Tuple[WorldRoute, WorldRoute, WorldRoute, WorldRoute]]:
    """
    Find four consecutive routes that form a GF(3)-balanced quad.
    
    A balanced quad has sum of all trits ≡ 0 (mod 3).
    """
    chain = derive_world_chain(seed, start_depth + 100)
    
    for i in range(len(chain) - 3):
        quad = chain[i:i+4] if hasattr(chain, '__getitem__') else [chain.routes[j] for j in range(i, i+4)]
        all_trits = []
        for route in quad:
            all_trits.extend(route.trits)
        
        if sum(all_trits) % 3 == 0:
            return tuple(quad)
    
    return None


# Goblin integration helpers
def pattern_to_goblin_indices(pattern: ThreeMatch) -> List[int]:
    """
    Map a three-match to goblin indices (0-25).
    
    Each trit maps to a goblin index:
        +1 → indices 0, 3, 6, 9, ... (mod 3 == 0)
        -1 → indices 1, 4, 7, 10, ... (mod 3 == 1)
         0 → indices 2, 5, 8, 11, ... (mod 3 == 2)
    """
    indices = []
    for i, trit in enumerate(pattern.trits):
        # Map trit to mod-3 class
        if trit == 1:
            mod_class = 0
        elif trit == -1:
            mod_class = 1
        else:  # trit == 0
            mod_class = 2
        
        # Deterministic selection within class
        goblin_idx = mod_class + (3 * ((pattern.depth + i) % 9))
        if goblin_idx < 26:
            indices.append(goblin_idx)
        else:
            indices.append(mod_class)  # Fallback
    
    return indices
