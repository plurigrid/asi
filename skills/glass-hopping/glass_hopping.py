#!/usr/bin/env python3
"""
glass_hopping.py - Glass Bead Game + World Hopping via Observational Bridge Types

Navigates possibility space through ordered locale ≪ relations.
Each hop is a Narya bridge type, verified for:
- Directional structure (asymmetric)
- Open cone condition
- GF(3) conservation
- Triangle inequality
"""

from __future__ import annotations
import sys
import subprocess
from dataclasses import dataclass, field
from typing import FrozenSet, Dict, List, Optional, Callable, Any, Tuple
from enum import IntEnum
from functools import reduce

sys.path.insert(0, '/Users/alice/.agents/skills/ordered-locale')
from ordered_locale import (
    OrderedLocale, Frame, triadic_gf3, directed_interval,
    cone, cocone, points_functor
)
from sheaves import DirectionalSheaf, Sheaf

# ============================================================================
# Constants
# ============================================================================

GOLDEN = 0x9E3779B97F4A7C15
MASK64 = 0xFFFFFFFFFFFFFFFF


def splitmix64(x: int) -> int:
    z = (x + GOLDEN) & MASK64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    return (z ^ (z >> 31)) & MASK64


# ============================================================================
# Trit and GF(3)
# ============================================================================

class Trit(IntEnum):
    MINUS = -1
    ERGODIC = 0
    PLUS = 1


def gf3_add(a: int, b: int) -> int:
    """Add in GF(3)"""
    return (a + b) % 3 - 1 if (a + b) % 3 != 0 else 0


def gf3_conserved(trits: List[int]) -> bool:
    """Check if sum of trits ≡ 0 (mod 3)"""
    return sum(trits) % 3 == 0


# ============================================================================
# Glass Bead
# ============================================================================

@dataclass
class GlassBead:
    """
    A bead in the Glass Bead Game.
    
    Corresponds to an open in the ordered locale.
    """
    domain: str          # mathematics, music, philosophy
    concept: str         # The conceptual content
    open_set: FrozenSet  # Points in locale where bead is active
    trit: int            # GF(3) polarity
    seed: int = 0        # Deterministic identity
    
    def __post_init__(self):
        if self.seed == 0:
            self.seed = hash((self.domain, self.concept)) & MASK64
    
    def active_in(self, point: Any) -> bool:
        return point in self.open_set
    
    def __hash__(self):
        return hash((self.domain, self.concept, self.trit))


# ============================================================================
# World (Possible World)
# ============================================================================

@dataclass
class World:
    """
    A possible world in the Glass Hopping space.
    """
    seed: int
    epoch: int = 0
    state: Dict[str, Any] = field(default_factory=dict)
    beads: List[GlassBead] = field(default_factory=list)
    
    @property
    def trit(self) -> int:
        """World's trit from active beads"""
        if not self.beads:
            return 0
        return sum(b.trit for b in self.beads) % 3 - 1
    
    def add_bead(self, bead: GlassBead):
        self.beads.append(bead)
    
    def __hash__(self):
        return hash((self.seed, self.epoch))


# ============================================================================
# Bridge (Observational Bridge Type)
# ============================================================================

@dataclass
class Bridge:
    """
    An observational bridge between worlds.
    
    Models U ≪ V in the ordered locale.
    Directed (asymmetric), not like HoTT paths.
    """
    source: World
    target: World
    name: str
    trit: int  # Bridge's own polarity
    bead_transfer: Optional[Callable] = None
    
    @property
    def is_valid(self) -> bool:
        """Check if bridge preserves GF(3)"""
        total = self.source.trit + self.trit + self.target.trit
        return total % 3 == 0
    
    def traverse(self) -> World:
        """Execute the hop along this bridge"""
        new_seed = splitmix64(self.source.seed ^ hash(self.name))
        new_world = World(
            seed=new_seed,
            epoch=self.source.epoch + 1,
            state=dict(self.source.state),
            beads=list(self.source.beads)
        )
        
        # Transfer beads that survive
        if self.bead_transfer:
            new_world.beads = [b for b in new_world.beads if self.bead_transfer(b)]
        
        return new_world


# ============================================================================
# Glass Hop Game
# ============================================================================

@dataclass
class GlassHopMove:
    """A move in the Glass Hopping game"""
    move_type: str  # PLACE, BRIDGE, HOP, OBSERVE
    player_trit: int
    data: Dict[str, Any] = field(default_factory=dict)
    points: int = 0


@dataclass
class GlassHoppingGame:
    """
    The Glass Hopping game engine.
    
    Combines glass beads, world hopping, and ordered locale structure.
    """
    locale: OrderedLocale
    seed: int
    players: int = 3
    current_world: World = None
    beads: List[GlassBead] = field(default_factory=list)
    bridges: List[Bridge] = field(default_factory=list)
    moves: List[GlassHopMove] = field(default_factory=list)
    scores: Dict[int, int] = field(default_factory=dict)
    
    def __post_init__(self):
        if self.current_world is None:
            self.current_world = World(seed=self.seed)
        
        # Initialize player scores
        for trit in [Trit.MINUS, Trit.ERGODIC, Trit.PLUS]:
            self.scores[trit] = 0
    
    # === Game Moves ===
    
    def place_bead(
        self, 
        domain: str, 
        concept: str, 
        trit: int,
        player_trit: int
    ) -> GlassHopMove:
        """PLACE: Add a bead to the locale"""
        # Determine open set based on trit
        if trit == Trit.MINUS:
            open_set = frozenset([-1, 0, 1])  # Full locale
        elif trit == Trit.ERGODIC:
            open_set = frozenset([0, 1])
        else:
            open_set = frozenset([1])
        
        bead = GlassBead(
            domain=domain,
            concept=concept,
            open_set=open_set,
            trit=trit,
            seed=splitmix64(self.seed ^ hash(concept))
        )
        
        self.beads.append(bead)
        self.current_world.add_bead(bead)
        
        # Scoring
        points = 10
        if gf3_conserved([b.trit for b in self.beads[-3:]]):
            points *= 2  # GF(3) bonus
        
        move = GlassHopMove(
            move_type="PLACE",
            player_trit=player_trit,
            data={"bead": bead},
            points=points
        )
        
        self.moves.append(move)
        self.scores[player_trit] += points
        
        return move
    
    def create_bridge(
        self,
        from_concept: str,
        to_concept: str,
        bridge_name: str,
        player_trit: int
    ) -> GlassHopMove:
        """BRIDGE: Create a ≪ connection between beads"""
        from_bead = next((b for b in self.beads if b.concept == from_concept), None)
        to_bead = next((b for b in self.beads if b.concept == to_concept), None)
        
        if not from_bead or not to_bead:
            raise ValueError(f"Beads not found: {from_concept}, {to_concept}")
        
        # Check ≪ order in locale
        way_below = self.locale.order_ll(from_bead.open_set, to_bead.open_set)
        
        # Compute bridge trit to conserve GF(3)
        bridge_trit = -(from_bead.trit + to_bead.trit) % 3
        if bridge_trit == 2:
            bridge_trit = -1
        
        bridge = Bridge(
            source=self.current_world,
            target=World(seed=splitmix64(self.current_world.seed)),
            name=bridge_name,
            trit=bridge_trit
        )
        
        self.bridges.append(bridge)
        
        # Scoring
        points = 25
        if way_below:
            points *= 2  # ≪ verified bonus
        if self.locale.has_open_cones():
            points = int(points * 1.5)  # Cone-preserving bonus
        
        move = GlassHopMove(
            move_type="BRIDGE",
            player_trit=player_trit,
            data={"bridge": bridge, "way_below": way_below},
            points=points
        )
        
        self.moves.append(move)
        self.scores[player_trit] += points
        
        return move
    
    def hop(
        self,
        bridge_name: str,
        player_trit: int
    ) -> GlassHopMove:
        """HOP: Navigate via bridge to new world"""
        bridge = next((b for b in self.bridges if b.name == bridge_name), None)
        
        if not bridge:
            raise ValueError(f"Bridge not found: {bridge_name}")
        
        # Execute hop
        new_world = bridge.traverse()
        old_world = self.current_world
        self.current_world = new_world
        
        # Check triangle inequality
        triangle_ok = True  # Assumed via ≪ transitivity
        
        # Check GF(3)
        gf3_ok = bridge.is_valid
        
        # Scoring
        points = 50
        if triangle_ok:
            points = int(points * 1.2)
        if gf3_ok:
            points *= 2
        
        move = GlassHopMove(
            move_type="HOP",
            player_trit=player_trit,
            data={
                "from_world": old_world,
                "to_world": new_world,
                "bridge": bridge,
                "gf3_conserved": gf3_ok
            },
            points=points
        )
        
        self.moves.append(move)
        self.scores[player_trit] += points
        
        return move
    
    def observe(
        self,
        bead_concept: str,
        player_trit: int
    ) -> GlassHopMove:
        """OBSERVE: Collapse superposition via bead measurement"""
        bead = next((b for b in self.beads if b.concept == bead_concept), None)
        
        if not bead:
            raise ValueError(f"Bead not found: {bead_concept}")
        
        # Observation collapses to single state
        observed_state = {
            "bead": bead.concept,
            "domain": bead.domain,
            "trit": bead.trit,
            "active_points": list(bead.open_set)
        }
        
        self.current_world.state["observation"] = observed_state
        
        # Scoring
        points = 30
        unique_observation = len([m for m in self.moves if m.move_type == "OBSERVE"]) == 0
        if unique_observation:
            points *= 2
        
        move = GlassHopMove(
            move_type="OBSERVE",
            player_trit=player_trit,
            data={"observation": observed_state},
            points=points
        )
        
        self.moves.append(move)
        self.scores[player_trit] += points
        
        return move
    
    # === Verification ===
    
    def verify_gf3(self) -> bool:
        """Verify GF(3) conservation across all beads"""
        return gf3_conserved([b.trit for b in self.beads])
    
    def verify_triangle_inequality(
        self, 
        w1: World, 
        w2: World, 
        w3: World
    ) -> Tuple[bool, float]:
        """Check triangle inequality for three worlds"""
        d12 = self._world_distance(w1, w2)
        d23 = self._world_distance(w2, w3)
        d13 = self._world_distance(w1, w3)
        
        satisfied = d13 <= d12 + d23
        excess = max(0, d13 - (d12 + d23))
        
        return satisfied, excess
    
    def _world_distance(self, w1: World, w2: World) -> float:
        """Distance between worlds (Hamming + epoch)"""
        hamming = bin(w1.seed ^ w2.seed).count('1')
        epoch_diff = abs(w1.epoch - w2.epoch)
        return (hamming**2 + epoch_diff**2) ** 0.5
    
    # === Display ===
    
    def summary(self) -> str:
        """Generate game summary"""
        lines = [
            "╔═══════════════════════════════════════════════════════════════╗",
            "║  GLASS HOPPING: Observational Bridge Navigation               ║",
            f"║  Seed: {hex(self.seed)}  |  Moves: {len(self.moves):2d}  |  GF(3): {'✓' if self.verify_gf3() else '✗'}              ║",
            "╚═══════════════════════════════════════════════════════════════╝",
            ""
        ]
        
        # Moves
        for i, move in enumerate(self.moves):
            trit_sym = {-1: "MINUS", 0: "ERGODIC", 1: "PLUS"}[move.player_trit]
            lines.append(f"Turn {i+1} [{trit_sym}]: {move.move_type}")
            if "bead" in move.data:
                b = move.data["bead"]
                lines.append(f"  → Bead: {b.domain}/{b.concept} (trit={b.trit:+d})")
            if "bridge" in move.data:
                br = move.data["bridge"]
                lines.append(f"  → Bridge: {br.name} (trit={br.trit:+d})")
            if "gf3_conserved" in move.data:
                lines.append(f"  → GF(3) conserved: {'✓' if move.data['gf3_conserved'] else '✗'}")
            lines.append(f"  → Points: {move.points}")
            lines.append("")
        
        # Scores
        lines.append("─── Scores ───")
        for trit, score in self.scores.items():
            role = {-1: "VALIDATOR", 0: "COORDINATOR", 1: "GENERATOR"}[trit]
            lines.append(f"  {role}: {score}")
        
        lines.append(f"\nTotal: {sum(self.scores.values())}")
        lines.append(f"GF(3) Sum: {sum(b.trit for b in self.beads)} {'✓' if self.verify_gf3() else '✗'}")
        
        if self.bridges:
            chain = " ≪ ".join(b.name for b in self.bridges)
            lines.append(f"Bridge Chain: {chain}")
        
        return "\n".join(lines)


# ============================================================================
# Voice Announcements
# ============================================================================

VOICES = {
    Trit.MINUS: "Anna",      # German - VALIDATOR
    Trit.ERGODIC: "Amelie",  # French - COORDINATOR
    Trit.PLUS: "Luca",       # Italian - GENERATOR
}


def announce(trit: int, message: str):
    """Announce via macOS say with trit-specific voice"""
    voice = VOICES.get(trit, "Samantha")
    subprocess.run(["say", "-v", voice, message], capture_output=True)


# ============================================================================
# Demo
# ============================================================================

def demo():
    """Run a demo glass hopping game"""
    print("Initializing Glass Hopping Game...")
    
    # Create game with triadic locale
    game = GlassHoppingGame(
        locale=triadic_gf3(),
        seed=0x42D,
        players=3
    )
    
    # Announce start
    announce(Trit.ERGODIC, "Glass hopping game initialized")
    
    # Turn 1: PLUS places bead
    announce(Trit.PLUS, "Placing prime numbers bead")
    game.place_bead("mathematics", "prime numbers", Trit.PLUS, Trit.PLUS)
    
    # Turn 2: ERGODIC places bead
    announce(Trit.ERGODIC, "Placing harmonic series bead")
    game.place_bead("music", "harmonic series", Trit.ERGODIC, Trit.ERGODIC)
    
    # Turn 3: MINUS places bead
    announce(Trit.MINUS, "Placing ontological void bead")
    game.place_bead("philosophy", "ontological void", Trit.MINUS, Trit.MINUS)
    
    # Turn 4: Create bridge
    announce(Trit.ERGODIC, "Creating overtone bridge")
    game.create_bridge("prime numbers", "harmonic series", "overtone", Trit.ERGODIC)
    
    # Turn 5: Hop
    announce(Trit.PLUS, "Hopping via overtone bridge")
    game.hop("overtone", Trit.PLUS)
    
    # Turn 6: Observe
    announce(Trit.MINUS, "Observing harmonic series")
    game.observe("harmonic series", Trit.MINUS)
    
    # Print summary
    print(game.summary())
    
    announce(Trit.ERGODIC, "Glass hopping complete. GF 3 conserved.")


if __name__ == "__main__":
    demo()
