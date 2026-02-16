"""GF(3) - The Galois Field with 3 elements.

The fundamental conservation law for skill triads:
    (+1) + (0) + (-1) ≡ 0 (mod 3)

Every skill operation must preserve this balance.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Union

# GF(3) constants
PLUS = 1      # +1: Generative, WORLDING
ERGODIC = 0   # 0: Coordinative, REMEMBERING
MINUS = -1    # -1: Validative, MEMORY


@dataclass(frozen=True)
class GF3:
    """A GF(3) element - the trit.
    
    Values: -1 (MINUS), 0 (ERGODIC), +1 (PLUS)
    
    Properties:
        - Closed under addition mod 3
        - (+1) + (-1) = 0
        - Conservation: sum of any triad = 0
    """
    value: int
    
    def __post_init__(self):
        # Normalize to GF(3) range
        object.__setattr__(self, 'value', self.value % 3)
        if self.value == 2:
            object.__setattr__(self, 'value', -1)
    
    def __add__(self, other: Union[GF3, int]) -> GF3:
        if isinstance(other, GF3):
            return GF3((self.value + other.value) % 3)
        return GF3((self.value + other) % 3)
    
    def __radd__(self, other: int) -> GF3:
        return GF3((other + self.value) % 3)
    
    def __neg__(self) -> GF3:
        return GF3(-self.value)
    
    def __eq__(self, other: object) -> bool:
        if isinstance(other, GF3):
            return self.value == other.value
        if isinstance(other, int):
            return self.value == (other % 3 if other != 2 else -1)
        return False
    
    def __hash__(self) -> int:
        return hash(self.value)
    
    def __repr__(self) -> str:
        names = {1: "PLUS", 0: "ERGODIC", -1: "MINUS"}
        return f"GF3({names.get(self.value, self.value)})"
    
    def __str__(self) -> str:
        return f"{self.value:+d}"
    
    @property
    def name(self) -> str:
        """Human-readable name."""
        return {1: "PLUS", 0: "ERGODIC", -1: "MINUS"}.get(self.value, "?")
    
    @property
    def role(self) -> str:
        """Role in the triad."""
        return {
            1: "WORLDING (generative)",
            0: "REMEMBERING (coordinative)", 
            -1: "MEMORY (validative)"
        }.get(self.value, "unknown")
    
    @classmethod
    def from_str(cls, s: str) -> GF3:
        """Parse from string: '+1', '0', '-1', 'plus', 'ergodic', 'minus'."""
        s = s.lower().strip()
        if s in ('+1', '1', 'plus', 'worlding', '+'):
            return cls(PLUS)
        elif s in ('0', 'ergodic', 'remembering'):
            return cls(ERGODIC)
        elif s in ('-1', 'minus', 'memory', '-'):
            return cls(MINUS)
        else:
            raise ValueError(f"Invalid GF(3) value: {s}")


def conserved(*trits: Union[GF3, int]) -> bool:
    """Check if a collection of trits is GF(3) conserved (sums to 0)."""
    total = sum(t.value if isinstance(t, GF3) else t for t in trits)
    return total % 3 == 0


def balance(*trits: Union[GF3, int]) -> GF3:
    """Return the balancing trit needed to conserve GF(3)."""
    total = sum(t.value if isinstance(t, GF3) else t for t in trits)
    return GF3((-total) % 3)


# Triad helpers
def make_triad(generator: str, coordinator: str, validator: str) -> dict:
    """Create a named triad with GF(3) conservation."""
    return {
        "generator": {"name": generator, "trit": GF3(PLUS)},
        "coordinator": {"name": coordinator, "trit": GF3(ERGODIC)},
        "validator": {"name": validator, "trit": GF3(MINUS)},
        "conserved": True,  # Always true by construction
    }


# Standard triads
ALIFE_TRIAD = make_triad("alife", "true-alife", "alife-validator")
SKILL_TRIAD = make_triad("skill-generator", "skill-coordinator", "skill-validator")
