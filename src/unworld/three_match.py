"""
ThreeMatch: The fundamental gadget of unworld.

A three-match is a GF(3)-balanced triad of colors:
    [trit:-1, trit:0, trit:+1] where sum ≡ 0 (mod 3)

This corresponds to Spivak's 'm' in the bicomodule c ⊲ m ⊲ d.
"""

from dataclasses import dataclass
from typing import List, Tuple

from .splitmix64 import (
    splitmix64_at,
    value_to_hue,
    value_to_saturation,
    value_to_lightness,
    value_to_trit,
    hsl_to_hex,
)


@dataclass
class Color:
    """A color with its GF(3) trit assignment."""
    
    value: int       # Raw 64-bit value
    hex: str         # Hex color string
    hue: float       # Hue in [0, 360)
    saturation: float
    lightness: float
    trit: int        # GF(3) trit: -1, 0, or +1
    index: int       # Position in genesis sequence
    
    @classmethod
    def from_value(cls, value: int, index: int) -> "Color":
        """Create a Color from a raw 64-bit value."""
        hue = value_to_hue(value)
        sat = value_to_saturation(value)
        lit = value_to_lightness(value)
        trit = value_to_trit(value)
        hex_str = hsl_to_hex(hue, sat, lit)
        
        return cls(
            value=value,
            hex=hex_str,
            hue=hue,
            saturation=sat,
            lightness=lit,
            trit=trit,
            index=index,
        )
    
    def __repr__(self) -> str:
        trit_sym = {-1: "−", 0: "○", 1: "+"}[self.trit]
        return f"Color({self.hex}, trit={trit_sym})"


@dataclass
class ThreeMatch:
    """
    A GF(3)-balanced triad of colors.
    
    This is the fundamental gadget of unworld, corresponding to
    Spivak's 'm' in the bicomodule structure c ⊲ m ⊲ d.
    
    Invariant: sum(trits) ≡ 0 (mod 3)
    """
    
    genesis_seed: int
    depth: int  # Position in derivation chain
    colors: Tuple[Color, Color, Color]
    
    def __post_init__(self):
        """Validate GF(3) conservation."""
        if not self.is_balanced():
            raise ValueError(
                f"ThreeMatch violates GF(3): trits={self.trits}, sum={sum(self.trits)}"
            )
    
    @classmethod
    def derive(cls, genesis_seed: int, depth: int) -> "ThreeMatch":
        """
        Derive a three-match at a specific depth.
        
        This is the σ (effect handler) operation:
            σ: m ⊲ d → c ⊲ m
        
        We generate 3 colors at indices [3*depth, 3*depth+1, 3*depth+2]
        and balance the third to ensure GF(3) conservation.
        """
        base_index = 3 * depth
        
        # Generate first two colors naturally
        v0 = splitmix64_at(genesis_seed, base_index)
        v1 = splitmix64_at(genesis_seed, base_index + 1)
        v2 = splitmix64_at(genesis_seed, base_index + 2)
        
        c0 = Color.from_value(v0, base_index)
        c1 = Color.from_value(v1, base_index + 1)
        
        # Adjust v2 to ensure GF(3) balance
        # We need: (t0 + t1 + t2) ≡ 0 (mod 3)
        # So: t2 ≡ -(t0 + t1) (mod 3)
        required_trit = (-(c0.trit + c1.trit)) % 3
        if required_trit == 2:
            required_trit = -1  # Map back to our trit range
        
        # Adjust v2 to produce required trit
        # value % 3 → trit:  0 → -1, 1 → 0, 2 → +1
        # So we need value % 3 == required_trit + 1
        target_mod = (required_trit + 1) % 3
        current_mod = v2 % 3
        adjustment = (target_mod - current_mod) % 3
        v2_adjusted = v2 - (v2 % 3) + target_mod
        
        c2 = Color.from_value(v2_adjusted, base_index + 2)
        
        return cls(
            genesis_seed=genesis_seed,
            depth=depth,
            colors=(c0, c1, c2),
        )
    
    @property
    def trits(self) -> List[int]:
        """Get the trits of all colors."""
        return [c.trit for c in self.colors]
    
    @property
    def hexes(self) -> List[str]:
        """Get the hex strings of all colors."""
        return [c.hex for c in self.colors]
    
    def is_balanced(self) -> bool:
        """Check if this three-match conserves GF(3)."""
        return sum(self.trits) % 3 == 0
    
    def trit_sum(self) -> int:
        """Get the sum of trits (should be 0, 3, -3, etc.)."""
        return sum(self.trits)
    
    def __repr__(self) -> str:
        trits = "".join({-1: "−", 0: "○", 1: "+"}[t] for t in self.trits)
        return f"ThreeMatch(depth={self.depth}, trits=[{trits}], balanced={self.is_balanced()})"
    
    def to_dict(self) -> dict:
        """Convert to dictionary for serialization."""
        return {
            "genesis_seed": hex(self.genesis_seed),
            "depth": self.depth,
            "colors": [
                {"hex": c.hex, "trit": c.trit, "index": c.index}
                for c in self.colors
            ],
            "trits": self.trits,
            "balanced": self.is_balanced(),
        }
