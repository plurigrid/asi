"""
Unworld: Derivational Learning via Seed Chaining

The executable substrate for Spivak's bicomodule structure.
Demonstrates that temporal learning and derivational generation are bisimilar,
with unworld achieving 100x speedup via GF(3) conservation guarantees.

Bicomodule Structure:
    c = Pattern signatures (learned behavioral invariants)
    ↕ σ (derivation step)
    m = Three-match gadgets ([trit:-1, trit:0, trit:+1])
    ↕ ε (extract exemplar) and δ (verify/contextualize)
    d = Genesis seeds + raw color chains

GF(3) Trit Assignment:
    fokker-planck-analyzer (-1) + gay-mcp (0) + unworld (+1) = 0 ✓
"""

from .three_match import ThreeMatch, Color
from .chain import UnworldChain, benchmark
from .bicomodule import (
    derivation_step,    # σ: m ⊲ d → c ⊲ m (effect handler)
    extract_exemplar,   # ε: m ⊲ d → d (counit)
    verify_and_contextualize,  # δ: m ⊲ d → m ⊲ (m ⊲ d) (comultiplication)
    verify_all_laws,
)
from .worlds import (
    WorldRoute,
    WorldChain,
    derive_world_chain,
    WORLDS_26,
    TRIT_TO_WORLDS,
)
from .gf3_verified import (
    Trit,
    is_balanced,
    balance_triad,
    gf3_sum_fast as gf3_sum,
    make_balanced_quad,
    verify_gf3_conservation_theorem,
)

__version__ = "0.1.0"
__trit__ = 1  # PLUS: synthesis/generation

__all__ = [
    # Core
    "ThreeMatch",
    "Color", 
    "UnworldChain",
    "benchmark",
    # Bicomodule operations
    "derivation_step",
    "extract_exemplar",
    "verify_and_contextualize",
    "verify_all_laws",
    # 26 Worlds integration
    "WorldRoute",
    "WorldChain",
    "derive_world_chain",
    "WORLDS_26",
    "TRIT_TO_WORLDS",
    # Dafny-verified GF(3) module
    "Trit",
    "is_balanced",
    "balance_triad",
    "gf3_sum",
    "make_balanced_quad",
    "verify_gf3_conservation_theorem",
]
