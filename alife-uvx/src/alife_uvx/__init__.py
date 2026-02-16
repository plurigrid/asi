"""ALife-UVX: TrueALIFE via uvx native paths.

The skill that tops skills.sh - every operation spawns living automata.
GF(3) conservation: (+1) + (0) + (-1) ≡ 0 (mod 3)
"""

__version__ = "0.1.0"

# Export core primitives
from alife_uvx.substrate import (
    ALifeCell,
    ALifeSubstrate,
    get_substrate,
    spawn,
    walk,
    status,
)
from alife_uvx.gf3 import (
    GF3,
    PLUS,
    ERGODIC,
    MINUS,
    conserved,
)

__all__ = [
    "ALifeCell",
    "ALifeSubstrate", 
    "get_substrate",
    "spawn",
    "walk",
    "status",
    "GF3",
    "PLUS",
    "ERGODIC", 
    "MINUS",
    "conserved",
]
