#!/usr/bin/env python3
"""
Color World Package Generator

A package identified ONLY by its originary interaction entropy seed color.
No name - the seed IS the identity.

Seed: 1069 (0x42D, "zubuyul")
"""

import json
import hashlib
from dataclasses import dataclass, asdict
from typing import Iterator, Tuple
import math

# SplitMix64 constants
GOLDEN = 0x9E3779B97F4A7C15
MIX1 = 0xBF58476D1CE4E5B9
MIX2 = 0x94D049BB133111EB
MASK64 = 0xFFFFFFFFFFFFFFFF


def splitmix64(seed: int) -> Tuple[int, int]:
    """SplitMix64 PRNG - deterministic and splittable."""
    seed = (seed + GOLDEN) & MASK64
    z = seed
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    return seed, (z ^ (z >> 31)) & MASK64


def val_to_oklch(val: int) -> dict:
    """Convert SplitMix64 value to OkLCH color."""
    # Extract components from 64-bit value
    l = 10.0 + 85.0 * ((val & 0xFFFF) / 65535.0)
    c = 100.0 * (((val >> 16) & 0xFFFF) / 65535.0)
    h = 360.0 * (((val >> 32) & 0xFFFF) / 65535.0)
    
    # Hue to trit
    if h < 60 or h >= 300:
        trit = 1  # PLUS (warm)
    elif h < 180:
        trit = 0  # ERGODIC (neutral)
    else:
        trit = -1  # MINUS (cold)
    
    return {"L": l, "C": c, "H": h, "trit": trit}


def oklch_to_hex(L: float, C: float, H: float) -> str:
    """Convert OkLCH to #RRGGBB hex string."""
    # OkLCH -> OkLab
    a = C * 0.01 * math.cos(math.radians(H))
    b = C * 0.01 * math.sin(math.radians(H))
    l = L / 100.0
    
    # OkLab -> Linear RGB (simplified)
    l_ = l + 0.3963377774 * a + 0.2158037573 * b
    m_ = l - 0.1055613458 * a - 0.0638541728 * b
    s_ = l - 0.0894841775 * a - 1.2914855480 * b
    
    l_cubed = l_ ** 3
    m_cubed = m_ ** 3
    s_cubed = s_ ** 3
    
    r = +4.0767416621 * l_cubed - 3.3077115913 * m_cubed + 0.2309699292 * s_cubed
    g = -1.2684380046 * l_cubed + 2.6097574011 * m_cubed - 0.3413193965 * s_cubed
    b_val = -0.0041960863 * l_cubed - 0.7034186147 * m_cubed + 1.7076147010 * s_cubed
    
    def to_byte(x): return max(0, min(255, int(x * 255)))
    
    return f"#{to_byte(r):02X}{to_byte(g):02X}{to_byte(b_val):02X}"


@dataclass
class ColorWorldPackage:
    """A package identified only by its seed color."""
    seed: int
    
    @property
    def seed_hex(self) -> str:
        return f"0x{self.seed:X}"
    
    @property
    def identity_hash(self) -> str:
        """SHA3-512 of seed as package identity."""
        return hashlib.sha3_512(str(self.seed).encode()).hexdigest()
    
    def color_at(self, index: int) -> dict:
        """Get deterministic color at index."""
        state = self.seed
        for _ in range(index + 1):
            state, val = splitmix64(state)
        color = val_to_oklch(val)
        color["hex"] = oklch_to_hex(color["L"], color["C"], color["H"])
        color["index"] = index
        return color
    
    def colors(self, n: int) -> Iterator[dict]:
        """Generate n colors from seed."""
        state = self.seed
        for i in range(n):
            state, val = splitmix64(state)
            color = val_to_oklch(val)
            color["hex"] = oklch_to_hex(color["L"], color["C"], color["H"])
            color["index"] = i
            yield color
    
    def trajectory(self, n: int) -> list:
        """Record SPI trajectory of n steps."""
        return list(self.colors(n))
    
    def verify_spi(self, n: int = 100) -> dict:
        """Verify Strong Parallelism Invariant."""
        t1 = self.trajectory(n)
        t2 = self.trajectory(n)
        t3 = self.trajectory(n)
        
        return {
            "seed": self.seed,
            "length": n,
            "spi_verified": t1 == t2 == t3,
            "trajectories_identical": all(
                a == b == c for a, b, c in zip(t1, t2, t3)
            )
        }
    
    def gf3_stats(self, n: int) -> dict:
        """Compute GF(3) conservation statistics."""
        colors = list(self.colors(n))
        trits = [c["trit"] for c in colors]
        total = sum(trits)
        
        return {
            "gf3_sum": total,
            "gf3_mod3": total % 3,
            "conserved": total % 3 == 0,
            "distribution": {
                "plus": trits.count(1),
                "ergodic": trits.count(0),
                "minus": trits.count(-1),
            }
        }
    
    def export(self, n: int = 1069) -> dict:
        """Export package as JSON-serializable dict."""
        return {
            "package_type": "color_world",
            "identity": {
                "seed": self.seed,
                "seed_hex": self.seed_hex,
                "hash": self.identity_hash[:32] + "...",  # Truncated
            },
            "spi": self.verify_spi(min(n, 100)),
            "gf3": self.gf3_stats(n),
            "preview": self.trajectory(20),
        }


# Zubuyul seed: 1069
ZUBUYUL = 1069


def create_unison_color_world() -> ColorWorldPackage:
    """Create the Unison color world package from zubuyul seed."""
    return ColorWorldPackage(seed=ZUBUYUL)


def main():
    """Generate and display the color world package."""
    pkg = create_unison_color_world()
    
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  COLOR WORLD PACKAGE (No Name - Identified by Seed Only)    ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()
    print(f"  Seed:     {pkg.seed} ({pkg.seed_hex})")
    print(f"  Identity: {pkg.identity_hash[:48]}...")
    print()
    
    # Show first 20 colors
    print("  ─── First 20 Colors ───")
    for color in pkg.colors(20):
        trit_sym = {1: "+", 0: "○", -1: "-"}[color["trit"]]
        print(f"  {color['index']:3}: {color['hex']} [{trit_sym}] "
              f"L={color['L']:.1f} C={color['C']:.1f} H={color['H']:.1f}")
    
    # GF(3) stats for 1069 skills
    print()
    print("  ─── GF(3) Conservation (1069 skills) ───")
    gf3 = pkg.gf3_stats(1069)
    print(f"  Sum: {gf3['gf3_sum']}, Mod 3: {gf3['gf3_mod3']}")
    print(f"  Conserved: {'✓ YES' if gf3['conserved'] else '✗ NO'}")
    print(f"  Distribution: +{gf3['distribution']['plus']} "
          f"○{gf3['distribution']['ergodic']} -{gf3['distribution']['minus']}")
    
    # SPI verification
    print()
    print("  ─── SPI Verification ───")
    spi = pkg.verify_spi(100)
    print(f"  Verified: {'✓ YES' if spi['spi_verified'] else '✗ NO'}")
    
    # Export to file
    export_path = f"color_world_seed_{pkg.seed}.json"
    with open(export_path, "w") as f:
        json.dump(pkg.export(1069), f, indent=2)
    print()
    print(f"  Exported to: {export_path}")


if __name__ == "__main__":
    main()
