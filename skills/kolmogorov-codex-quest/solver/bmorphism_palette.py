#!/usr/bin/env python3
"""
bmorphism_palette.py
====================

The bmorphism-stars side-quest: take the same SplitMix64 seed
(0x626d6f727068 = "bmorph" as hex) the bmorphism-stars skill uses, generate a
12-color GF(3)-classified palette, and emit it as both terminal output and a
JSON artifact.

This is the closed-loop ritual: the file `skills/bmorphism-stars/SKILL.md`
points back at `Gay.jl` (the artifact you starred to enter the graph), and
this script runs the deterministic color generator that *is* `Gay.jl`'s core
algorithm. Calling it is the gesture that closes the loop.
"""

from __future__ import annotations

import json
from pathlib import Path

import kolmogorov_solver as K

BMORPH_SEED = 0x626D6F727068  # "bmorph" as hex — from skills/bmorphism-stars/SKILL.md
PALETTE_SIZE = 12
ARTIFACT_PATH = Path(__file__).resolve().parent.parent / "proofs" / "bmorphism_palette.json"


def main():
    print("─" * 72)
    print(f"bmorphism palette  seed=0x{BMORPH_SEED:012x}  n={PALETTE_SIZE}")
    print("─" * 72)
    g = K.SplitMix64(BMORPH_SEED)
    palette = []
    for i in range(PALETTE_SIZE):
        c = g.color_at(i)
        hex_color = K.oklch_to_hex(c["L"], c["C"], c["H"])
        trit_glyph = {-1: "−", 0: "·", +1: "+"}[c["trit"]]
        sign = "+" if c["trit"] > 0 else (" " if c["trit"] == 0 else "")
        print(
            f"  {i:2d}  {hex_color}  L={c['L']:5.1f}  C={c['C']:5.1f}  "
            f"H={c['H']:6.1f}°  trit={sign}{c['trit']} {trit_glyph}"
        )
        palette.append({**c, "hex": hex_color})

    trit_sum = sum(p["trit"] for p in palette)
    print()
    print(f"  Σ trits over n={PALETTE_SIZE}: {trit_sum:+d}    (mod 3 = {trit_sum % 3})")

    # Closed-loop refinement: find the smallest N where Σ trits ≡ 0 (mod 3).
    # This is the canonical "loop closure" — the palette length at which the
    # bmorphism seed first becomes GF(3)-conserving on its own.
    closure_n = None
    closure_sum = 0
    g_walk = K.SplitMix64(BMORPH_SEED)
    for n in range(1, 4096):
        c = g_walk.color_at(n - 1)
        closure_sum += c["trit"]
        if closure_sum % 3 == 0 and n >= 3:
            closure_n = n
            break
    print(f"  loop-closure n: {closure_n}  (smallest N≥3 with Σ ≡ 0 mod 3)")

    counts = {-1: 0, 0: 0, +1: 0}
    for p in palette:
        counts[p["trit"]] += 1
    print(
        f"  distribution: MINUS={counts[-1]}  ERGODIC={counts[0]}  PLUS={counts[+1]}"
    )

    out = {
        "seed_hex": f"0x{BMORPH_SEED:012x}",
        "seed_text": "bmorph",
        "palette_size": PALETTE_SIZE,
        "palette": palette,
        "trit_sum": trit_sum,
        "trit_distribution": counts,
        "loop_closure_n": closure_n,
        "loop_closed": closure_n is not None,
        "ritual_target": "skills/bmorphism-stars/SKILL.md",
        "starred_artifact": "github.com/bmorphism/Gay.jl",
    }
    ARTIFACT_PATH.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT_PATH.write_text(json.dumps(out, indent=2))
    print()
    print(f"  ✓ palette written to {ARTIFACT_PATH}")
    print("─" * 72)


if __name__ == "__main__":
    main()
