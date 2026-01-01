#!/usr/bin/env python3
"""
terminal_cantordust.py - Braille-based binary visualization

Renders Cantordust 2-tuple plots directly in terminal using:
- Braille unicode characters (⠀ to ⣿)
- Gay.jl deterministic colors via ANSI escape codes
- GF(3) entropy classification

Usage:
    python terminal_cantordust.py <binary_file>
    cat binary | python terminal_cantordust.py -
"""

import sys
import os
from collections import defaultdict
from typing import Tuple, List

# Braille patterns: 2x4 dots encoded as bits
# ⠀ = 0x2800, each dot adds: ⠁=1, ⠂=2, ⠄=4, ⠈=8, ⠐=16, ⠠=32, ⡀=64, ⢀=128
BRAILLE_BASE = 0x2800

# SplitMix64 for Gay.jl colors
GOLDEN = 0x9e3779b97f4a7c15

class SplitMix64:
    def __init__(self, seed: int):
        self.state = seed & 0xFFFFFFFFFFFFFFFF
    
    def next(self) -> int:
        self.state = (self.state + GOLDEN) & 0xFFFFFFFFFFFFFFFF
        z = self.state
        z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & 0xFFFFFFFFFFFFFFFF
        z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & 0xFFFFFFFFFFFFFFFF
        return z ^ (z >> 31)
    
    def next_hue(self) -> float:
        """Golden angle hue (137.508°)"""
        return (self.next() / (2**64)) * 360


def hsl_to_ansi(h: float, s: float = 0.7, l: float = 0.55) -> str:
    """Convert HSL to ANSI 256-color escape code."""
    c = (1 - abs(2*l - 1)) * s
    x = c * (1 - abs((h/60) % 2 - 1))
    m = l - c/2
    
    if h < 60: r, g, b = c, x, 0
    elif h < 120: r, g, b = x, c, 0
    elif h < 180: r, g, b = 0, c, x
    elif h < 240: r, g, b = 0, x, c
    elif h < 300: r, g, b = x, 0, c
    else: r, g, b = c, 0, x
    
    r8 = int((r + m) * 255)
    g8 = int((g + m) * 255)
    b8 = int((b + m) * 255)
    
    return f"\033[38;2;{r8};{g8};{b8}m"


def two_tuple_matrix(data: bytes) -> List[List[int]]:
    """Generate 256x256 2-tuple frequency matrix."""
    matrix = [[0] * 256 for _ in range(256)]
    for i in range(len(data) - 1):
        x, y = data[i], data[i+1]
        matrix[y][x] += 1  # Note: y is row, x is col
    return matrix


def entropy_region(data: bytes, offset: int, size: int = 32) -> float:
    """Calculate entropy of a region."""
    window = data[offset:offset+size]
    if len(window) < 8:
        return 0.0
    
    counts = [0] * 256
    for b in window:
        counts[b] += 1
    
    entropy = 0.0
    for c in counts:
        if c > 0:
            p = c / len(window)
            entropy -= p * (p and __import__('math').log2(p))
    
    return entropy / 8.0  # Normalize to [0, 1]


def entropy_to_trit(entropy: float) -> int:
    """Map entropy to GF(3) trit."""
    if entropy < 0.3: return -1  # Structured
    if entropy > 0.7: return 1   # Random
    return 0                      # Mixed


def matrix_to_braille(matrix: List[List[int]], width: int = 48, height: int = 16) -> List[str]:
    """Convert 256x256 matrix to braille grid."""
    # Scale factor: each braille char is 2x4 dots
    x_scale = 256 / (width * 2)
    y_scale = 256 / (height * 4)
    
    max_val = max(max(row) for row in matrix) or 1
    
    lines = []
    for row in range(height):
        line = ""
        for col in range(width):
            # Collect 2x4 dots
            dots = 0
            for dy in range(4):
                for dx in range(2):
                    mx = int((col * 2 + dx) * x_scale)
                    my = int((row * 4 + dy) * y_scale)
                    if mx < 256 and my < 256:
                        val = matrix[my][mx]
                        # Threshold: show dot if frequency > 0
                        if val > 0:
                            # Braille dot mapping
                            bit = [0, 3, 1, 4, 2, 5, 6, 7][dy * 2 + dx]
                            dots |= (1 << bit)
            
            line += chr(BRAILLE_BASE + dots)
        lines.append(line)
    
    return lines


def colorize_braille(lines: List[str], seed: int = 0x1069) -> List[str]:
    """Apply Gay.jl colors to braille lines."""
    rng = SplitMix64(seed)
    colored = []
    
    for i, line in enumerate(lines):
        hue = rng.next_hue()
        color = hsl_to_ansi(hue)
        colored.append(f"{color}{line}\033[0m")
    
    return colored


def render_cantordust(data: bytes, width: int = 48, height: int = 16, seed: int = 0x1069) -> str:
    """Full terminal Cantordust render."""
    matrix = two_tuple_matrix(data)
    lines = matrix_to_braille(matrix, width, height)
    colored = colorize_braille(lines, seed)
    
    # Stats
    nonzero = sum(1 for row in matrix for v in row if v > 0)
    diagonal = sum(matrix[i][i] for i in range(256))
    total = sum(sum(row) for row in matrix) or 1
    diagonal_score = diagonal / total
    
    # ASCII region (0x20-0x7F)
    ascii_sum = sum(matrix[y][x] for y in range(0x20, 0x80) for x in range(0x20, 0x80))
    ascii_score = ascii_sum / total
    
    # Entropy analysis
    n_regions = len(data) // 32
    trits = [entropy_to_trit(entropy_region(data, i*32)) for i in range(n_regions)]
    trit_sum = sum(trits)
    
    # Build output
    output = []
    output.append(f"\n🔬 Terminal Cantordust ({len(data)} bytes)")
    output.append("=" * (width + 2))
    
    for line in colored:
        output.append(f"│{line}│")
    
    output.append("=" * (width + 2))
    output.append(f"Cells: {nonzero}/65536 | Diagonal: {diagonal_score:.3f} | ASCII: {ascii_score:.3f}")
    output.append(f"GF(3): Σtrit={trit_sum} (balanced={trit_sum % 3 == 0})")
    output.append("Legend: Brightness = frequency, Color = Gay.jl golden angle")
    
    return "\n".join(output)


def main():
    if len(sys.argv) < 2:
        print("Usage: python terminal_cantordust.py <binary_file>")
        print("       cat binary | python terminal_cantordust.py -")
        sys.exit(1)
    
    path = sys.argv[1]
    
    if path == "-":
        data = sys.stdin.buffer.read()
    else:
        with open(path, "rb") as f:
            data = f.read()
    
    # Seed from filename or default
    seed = hash(path) & 0xFFFFFFFFFFFFFFFF if path != "-" else 0x1069
    
    print(render_cantordust(data, seed=seed))


if __name__ == "__main__":
    main()
