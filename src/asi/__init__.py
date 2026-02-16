"""
Plurigrid ASI - Algebraic Superintelligence

A category-theoretic skill framework implementing the bicomodule pattern
with GF(3) conservation for compositional AI systems.

Core concepts:
- Skills: 365 capabilities with GF(3) trit assignments
- Bicomodule: c ↔ m ↔ d layered architecture
- SPI Colors: Deterministic LCH colors from seed (1069 canonical)
- TAP Control: Backfill(-1) | Verify(0) | Live(+1)
"""

__version__ = "0.1.0"
__author__ = "Plurigrid"

# GF(3) trit values
PLUS = 1      # Generation, synthesis, forward
ERGODIC = 0   # Coordination, balance, transport
MINUS = -1    # Verification, validation, backward

# Canonical seed for deterministic colors
CANONICAL_SEED = 1069

# Skill categories by trit
TRIT_CATEGORIES = {
    PLUS: "Generation/Synthesis",
    ERGODIC: "Coordination/Infrastructure", 
    MINUS: "Verification/Validation",
}
