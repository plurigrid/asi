"""
SplitMix64: The deterministic PRNG underlying all of unworld.

Same seed + same index = same output, always.
This is what makes derivational learning possible.

Reference: https://xoshiro.di.unimi.it/splitmix64.c
"""

from typing import Tuple

# SplitMix64 constants
GOLDEN_GAMMA = 0x9e3779b97f4a7c15
MIX1 = 0xbf58476d1ce4e5b9
MIX2 = 0x94d049bb133111eb
MASK64 = 0xFFFFFFFFFFFFFFFF


def splitmix64_next(state: int) -> Tuple[int, int]:
    """
    Advance state and produce next random value.
    
    Returns:
        (next_state, random_value)
    """
    state = (state + GOLDEN_GAMMA) & MASK64
    z = state
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    z = (z ^ (z >> 31)) & MASK64
    return state, z


def splitmix64_at(seed: int, index: int) -> int:
    """
    Get the value at a specific index without iterating.
    
    This uses the property that SplitMix64 has a simple
    relationship between state and output.
    
    Args:
        seed: The genesis seed
        index: The index in the sequence
    
    Returns:
        The deterministic value at that index
    """
    # Compute state at index
    state = (seed + (GOLDEN_GAMMA * index)) & MASK64
    
    # Mix
    z = state
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    z = (z ^ (z >> 31)) & MASK64
    
    return z


def value_to_hue(value: int) -> float:
    """Convert a 64-bit value to a hue in [0, 360)."""
    # Use lower 16 bits for hue
    return (value & 0xFFFF) / 0xFFFF * 360.0


def value_to_saturation(value: int) -> float:
    """Convert a 64-bit value to saturation in [0.5, 1.0]."""
    # Use bits 16-31 for saturation
    return 0.5 + ((value >> 16) & 0xFFFF) / 0xFFFF * 0.5


def value_to_lightness(value: int) -> float:
    """Convert a 64-bit value to lightness in [0.3, 0.7]."""
    # Use bits 32-47 for lightness
    return 0.3 + ((value >> 32) & 0xFFFF) / 0xFFFF * 0.4


def value_to_trit(value: int) -> int:
    """
    Extract GF(3) trit from value.
    
    Mapping: value % 3 → trit
        0 → -1 (MINUS)
        1 →  0 (ERGODIC)
        2 → +1 (PLUS)
    """
    return (value % 3) - 1


def hsl_to_hex(h: float, s: float, l: float) -> str:
    """Convert HSL to hex color string."""
    def hue2rgb(p: float, q: float, t: float) -> float:
        if t < 0: t += 1
        if t > 1: t -= 1
        if t < 1/6: return p + (q - p) * 6 * t
        if t < 1/2: return q
        if t < 2/3: return p + (q - p) * (2/3 - t) * 6
        return p

    h_norm = h / 360.0
    q = l * (1 + s) if l < 0.5 else l + s - l * s
    p = 2 * l - q
    
    r = int(hue2rgb(p, q, h_norm + 1/3) * 255)
    g = int(hue2rgb(p, q, h_norm) * 255)
    b = int(hue2rgb(p, q, h_norm - 1/3) * 255)
    
    return f"#{r:02X}{g:02X}{b:02X}"
