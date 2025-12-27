"""
Operads Module: Colored, Cyclic, and Modular Operads

Implements higher categorical structures for composition:
- ColoredSymmetricOperad: Σ-colored with typed inputs/outputs
- CyclicOperad: Z_{n+1} symmetric (no input/output distinction)
- ModularOperad: Genus-labeled for TQFT
- ThreadOperad: Integration with DiscoHy thread operad
"""

from .colored_cyclic_operads import (
    Color,
    ColoredSymmetricOperad,
    CyclicOperad,
    ModularOperad,
    ThreadOperad,
    ColoredOperation,
    CyclicOperation,
    ModularOperation,
    ThreadOperation,
    OperadMorphism,
    operad_to_discopy,
    operad_to_mermaid,
)

__all__ = [
    "Color",
    "ColoredSymmetricOperad",
    "CyclicOperad",
    "ModularOperad",
    "ThreadOperad",
    "ColoredOperation",
    "CyclicOperation",
    "ModularOperation",
    "ThreadOperation",
    "OperadMorphism",
    "operad_to_discopy",
    "operad_to_mermaid",
]
