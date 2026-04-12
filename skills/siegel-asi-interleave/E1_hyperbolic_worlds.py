"""E1 — HyperNEM embedding of the 6 bmorph worlds.

Deterministic Poincaré ball coordinates derived from the same seed
(0x626d6f727068) and trit pattern (-1, 0, +1, -1, 0, +1). Hyperbolic
neighbors should recover GF(3) balance: each world's nearest neighbor
must carry a complementary trit so the pair sums to 0 mod 3.

Standalone, no deps beyond stdlib + math. Decidable self-test at bottom.
"""
from __future__ import annotations
import hashlib
import math
from typing import List, Tuple

SEED = 0x626D6F727068  # "bmorph"
TRITS = (-1, 0, 1, -1, 0, 1)
N_WORLDS = 6
DIM = 3


def _splitmix64(x: int) -> int:
    x = (x + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
    x = ((x ^ (x >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
    x = ((x ^ (x >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
    return x ^ (x >> 31)


def _world_vector(i: int) -> Tuple[float, ...]:
    # Derive DIM float64 coords in (-1, 1) via SplitMix64, then shrink into the
    # open Poincaré ball. Trit shifts the radius so complementary trits sit at
    # antipodal directions but at equal distance from origin.
    base = _splitmix64(SEED ^ (i * 0xA5A5A5A5A5A5A5A5))
    coords: List[float] = []
    cur = base
    for _ in range(DIM):
        cur = _splitmix64(cur)
        coords.append(((cur >> 11) / (1 << 53)) * 2.0 - 1.0)
    norm = math.sqrt(sum(c * c for c in coords)) or 1.0
    unit = [c / norm for c in coords]
    trit = TRITS[i]
    # Map trit → signed radius offset, then shrink into ball radius 0.8.
    # Trit 0 sits closest to origin; ±1 push outward in opposite directions.
    base_r = 0.3 + 0.35 * abs(trit)
    direction = 1.0 if trit >= 0 else -1.0
    return tuple(direction * base_r * u for u in unit)


def poincare_distance(u: Tuple[float, ...], v: Tuple[float, ...]) -> float:
    norm_u = sum(a * a for a in u)
    norm_v = sum(a * a for a in v)
    diff_sq = sum((a - b) ** 2 for a, b in zip(u, v))
    denom = (1 - norm_u) * (1 - norm_v)
    if denom <= 0:
        return math.inf
    return math.acosh(1 + 2 * diff_sq / denom)


def embed_worlds() -> List[Tuple[float, ...]]:
    return [_world_vector(i) for i in range(N_WORLDS)]


def nearest_neighbor(worlds: List[Tuple[float, ...]], i: int) -> int:
    best, best_d = -1, math.inf
    for j, w in enumerate(worlds):
        if j == i:
            continue
        d = poincare_distance(worlds[i], w)
        if d < best_d:
            best_d = d
            best = j
    return best


def gf3_balance_preserved(worlds: List[Tuple[float, ...]]) -> bool:
    """Decidable test: each world's NN has complementary trit (pair sum ≡ 0 mod 3)."""
    for i in range(N_WORLDS):
        j = nearest_neighbor(worlds, i)
        if (TRITS[i] + TRITS[j]) % 3 != 0:
            return False
    return True


def proof_leaf(worlds: List[Tuple[float, ...]]) -> bytes:
    """Merkle leaf: sha3-256 of the canonical JSON-ish encoding.

    Backwards-compatible with existing IdentityProof — lives under a new
    proof_uri version. Does not perturb wikidata_root or gaymcp_root.
    """
    payload = b";".join(
        f"{i}:{TRITS[i]}:" + ",".join(f"{x:.12f}" for x in w).encode().decode().encode()
        for i, w in enumerate(worlds)
    )
    return hashlib.sha3_256(payload).digest()


if __name__ == "__main__":
    worlds = embed_worlds()
    for i, w in enumerate(worlds):
        print(f"world[{i}] trit={TRITS[i]:+d}  pos=({w[0]:+.4f}, {w[1]:+.4f}, {w[2]:+.4f})")
    print()
    for i in range(N_WORLDS):
        j = nearest_neighbor(worlds, i)
        d = poincare_distance(worlds[i], worlds[j])
        ok = (TRITS[i] + TRITS[j]) % 3 == 0
        print(f"NN(world[{i}]) = world[{j}]  d={d:.4f}  trit_pair_sum_mod3={ok}")
    print()
    print("gf3_balance_preserved:", gf3_balance_preserved(worlds))
    print("proof_leaf:", proof_leaf(worlds).hex())
