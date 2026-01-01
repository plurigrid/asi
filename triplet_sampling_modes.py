#!/usr/bin/env python3
"""Triplet Sampling Modes - Local simulation of Aptos on-chain randomness patterns.

Demonstrates 4 sampling modes for GF(3) skill triplets:
1. With replacement, with coloring
2. With replacement, without coloring  
3. Without replacement, with coloring
4. Without replacement, without coloring

Interaction entropy serves as the seed for deterministic color derivation.

Usage:
    python triplet_sampling_modes.py --mode all --count 5
    python triplet_sampling_modes.py --mode with_replacement --coloring
    python triplet_sampling_modes.py --entropy 0x6761795f636f6c6f
"""

import argparse
import hashlib
import random
from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict
from pathlib import Path
from enum import Enum
import re

# Genesis seed
GAY_SEED = 0x6761795f636f6c6f  # "gay_colo"


class Trit(Enum):
    MINUS = -1
    ERGODIC = 0
    PLUS = 1


@dataclass
class Skill:
    name: str
    trit: Trit
    
    def __hash__(self):
        return hash(self.name)


@dataclass
class Triplet:
    minus: Skill
    ergodic: Skill
    plus: Skill
    fingerprint: int = 0
    
    def __post_init__(self):
        if self.fingerprint == 0:
            self.fingerprint = self._compute_fingerprint()
    
    def _compute_fingerprint(self) -> int:
        h1 = int(hashlib.sha256(self.minus.name.encode()).hexdigest()[:16], 16)
        h2 = int(hashlib.sha256(self.ergodic.name.encode()).hexdigest()[:16], 16)
        h3 = int(hashlib.sha256(self.plus.name.encode()).hexdigest()[:16], 16)
        return h1 ^ h2 ^ h3
    
    @property
    def conserved(self) -> bool:
        return (self.minus.trit.value + self.ergodic.trit.value + self.plus.trit.value) % 3 == 0
    
    def __str__(self) -> str:
        return f"{self.minus.name} (-1) ⊗ {self.ergodic.name} (0) ⊗ {self.plus.name} (+1) = 0 ✓"


@dataclass
class SkillPool:
    minus: List[Skill] = field(default_factory=list)
    ergodic: List[Skill] = field(default_factory=list)
    plus: List[Skill] = field(default_factory=list)
    interaction_entropy: int = GAY_SEED
    
    @classmethod
    def from_skills_dir(cls, skills_dir: Path) -> "SkillPool":
        pool = cls()
        
        for skill_md in skills_dir.glob("*/SKILL.md"):
            name = skill_md.parent.name
            content = skill_md.read_text()
            
            # Extract trit
            match = re.search(r'trit:\s*([+-]?[01])', content)
            if match:
                trit_val = int(match.group(1))
                trit = Trit(trit_val)
            else:
                trit = Trit.ERGODIC
            
            skill = Skill(name, trit)
            
            if trit == Trit.MINUS:
                pool.minus.append(skill)
            elif trit == Trit.ERGODIC:
                pool.ergodic.append(skill)
            else:
                pool.plus.append(skill)
        
        return pool
    
    def stats(self) -> Tuple[int, int, int, int]:
        n_m, n_e, n_p = len(self.minus), len(self.ergodic), len(self.plus)
        return n_m, n_e, n_p, n_m * n_e * n_p


def splitmix64(x: int) -> int:
    """SplitMix64 bijection for deterministic hashing."""
    x = (x + 0x9e3779b97f4a7c15) & 0xFFFFFFFFFFFFFFFF
    x = ((x ^ (x >> 30)) * 0xbf58476d1ce4e5b9) & 0xFFFFFFFFFFFFFFFF
    x = ((x ^ (x >> 27)) * 0x94d049bb133111eb) & 0xFFFFFFFFFFFFFFFF
    return (x ^ (x >> 31)) & 0xFFFFFFFFFFFFFFFF


# ═══════════════════════════════════════════════════════════════════════════════
# Sampling Modes
# ═══════════════════════════════════════════════════════════════════════════════

def sample_with_replacement_with_coloring(
    pool: SkillPool,
    count: int,
    interaction_indices: List[int],
) -> List[Triplet]:
    """Sample triplets with replacement, using interaction entropy for coloring."""
    triplets = []
    
    for i, idx in enumerate(interaction_indices[:count]):
        # Mix entropy with interaction index
        seed = splitmix64(pool.interaction_entropy ^ idx)
        
        m_idx = seed % len(pool.minus)
        e_idx = (seed >> 16) % len(pool.ergodic)
        p_idx = (seed >> 32) % len(pool.plus)
        
        triplets.append(Triplet(
            pool.minus[m_idx],
            pool.ergodic[e_idx],
            pool.plus[p_idx]
        ))
    
    return triplets


def sample_with_replacement_without_coloring(
    pool: SkillPool,
    count: int,
    rng: Optional[random.Random] = None,
) -> List[Triplet]:
    """Sample triplets with replacement, pure random (no entropy mixing)."""
    if rng is None:
        rng = random.Random()
    
    triplets = []
    for _ in range(count):
        triplets.append(Triplet(
            rng.choice(pool.minus),
            rng.choice(pool.ergodic),
            rng.choice(pool.plus)
        ))
    
    return triplets


def sample_without_replacement_with_coloring(
    pool: SkillPool,
    count: int,
    interaction_indices: List[int],
) -> Tuple[List[Triplet], SkillPool]:
    """Sample triplets without replacement, using interaction entropy for ordering."""
    triplets = []
    
    # Create mutable copies
    minus = pool.minus.copy()
    ergodic = pool.ergodic.copy()
    plus = pool.plus.copy()
    
    for i, idx in enumerate(interaction_indices[:count]):
        if not minus or not ergodic or not plus:
            break
        
        # Deterministic selection via entropy
        seed = splitmix64(pool.interaction_entropy ^ idx)
        
        m_idx = seed % len(minus)
        e_idx = (seed >> 16) % len(ergodic)
        p_idx = (seed >> 32) % len(plus)
        
        triplets.append(Triplet(
            minus.pop(m_idx),
            ergodic.pop(e_idx),
            plus.pop(p_idx)
        ))
    
    # Return remaining pool
    remaining = SkillPool(minus, ergodic, plus, pool.interaction_entropy)
    return triplets, remaining


def sample_without_replacement_without_coloring(
    pool: SkillPool,
    count: int,
    rng: Optional[random.Random] = None,
) -> Tuple[List[Triplet], SkillPool]:
    """Sample triplets without replacement, pure random."""
    if rng is None:
        rng = random.Random()
    
    triplets = []
    
    minus = pool.minus.copy()
    ergodic = pool.ergodic.copy()
    plus = pool.plus.copy()
    
    rng.shuffle(minus)
    rng.shuffle(ergodic)
    rng.shuffle(plus)
    
    for _ in range(count):
        if not minus or not ergodic or not plus:
            break
        
        triplets.append(Triplet(
            minus.pop(),
            ergodic.pop(),
            plus.pop()
        ))
    
    remaining = SkillPool(minus, ergodic, plus, pool.interaction_entropy)
    return triplets, remaining


# ═══════════════════════════════════════════════════════════════════════════════
# Three at a time (batch mode)
# ═══════════════════════════════════════════════════════════════════════════════

def sample_three_at_once(
    pool: SkillPool,
    with_replacement: bool,
    with_coloring: bool,
    interaction_indices: Optional[List[int]] = None,
    rng: Optional[random.Random] = None,
) -> List[Triplet]:
    """Sample exactly 3 triplets at once (matches Aptos permutation pattern)."""
    if interaction_indices is None:
        interaction_indices = [0, 1, 2]
    
    if with_replacement:
        if with_coloring:
            return sample_with_replacement_with_coloring(pool, 3, interaction_indices)
        else:
            return sample_with_replacement_without_coloring(pool, 3, rng)
    else:
        if with_coloring:
            triplets, _ = sample_without_replacement_with_coloring(pool, 3, interaction_indices)
            return triplets
        else:
            triplets, _ = sample_without_replacement_without_coloring(pool, 3, rng)
            return triplets


# ═══════════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════════

def print_triplets(triplets: List[Triplet], mode: str):
    print(f"\n{mode}:")
    print("-" * 70)
    for t in triplets:
        print(f"  {t}")
    print()


def main():
    parser = argparse.ArgumentParser(description="GF(3) Triplet Sampling Modes")
    parser.add_argument("--mode", choices=["all", "with_replacement", "without_replacement"], 
                        default="all", help="Sampling mode")
    parser.add_argument("--coloring", action="store_true", help="Use interaction entropy coloring")
    parser.add_argument("--count", "-n", type=int, default=3, help="Number of triplets")
    parser.add_argument("--entropy", type=str, default=hex(GAY_SEED), 
                        help="Interaction entropy seed (hex)")
    parser.add_argument("--seed", type=int, default=42, help="Random seed for without-coloring modes")
    args = parser.parse_args()
    
    # Load skills
    skills_dir = Path(__file__).parent / "skills"
    pool = SkillPool.from_skills_dir(skills_dir)
    pool.interaction_entropy = int(args.entropy, 16)
    
    n_m, n_e, n_p, n_triplets = pool.stats()
    print("=" * 70)
    print("GF(3) TRIPLET SAMPLING MODES")
    print("=" * 70)
    print(f"MINUS (-1):   {n_m:>3} skills")
    print(f"ERGODIC (0):  {n_e:>3} skills")
    print(f"PLUS (+1):    {n_p:>3} skills")
    print(f"Possible:     {n_triplets:,} triplets")
    print(f"Entropy:      {hex(pool.interaction_entropy)}")
    print("=" * 70)
    
    # Generate interaction indices
    indices = list(range(args.count))
    rng = random.Random(args.seed)
    
    if args.mode == "all":
        # Demo all 4 modes
        print("\n1. WITH replacement, WITH coloring (deterministic from entropy):")
        triplets = sample_with_replacement_with_coloring(pool, args.count, indices)
        for t in triplets:
            print(f"   {t}")
        
        print("\n2. WITH replacement, WITHOUT coloring (pure random):")
        triplets = sample_with_replacement_without_coloring(pool, args.count, rng)
        for t in triplets:
            print(f"   {t}")
        
        print("\n3. WITHOUT replacement, WITH coloring (deterministic, unique):")
        triplets, remaining = sample_without_replacement_with_coloring(pool, args.count, indices)
        for t in triplets:
            print(f"   {t}")
        r_m, r_e, r_p, _ = remaining.stats()
        print(f"   Remaining: {r_m} MINUS, {r_e} ERGODIC, {r_p} PLUS")
        
        print("\n4. WITHOUT replacement, WITHOUT coloring (random, unique):")
        triplets, remaining = sample_without_replacement_without_coloring(pool, args.count, rng)
        for t in triplets:
            print(f"   {t}")
        r_m, r_e, r_p, _ = remaining.stats()
        print(f"   Remaining: {r_m} MINUS, {r_e} ERGODIC, {r_p} PLUS")
        
    else:
        with_replacement = args.mode == "with_replacement"
        
        if args.coloring:
            if with_replacement:
                triplets = sample_with_replacement_with_coloring(pool, args.count, indices)
            else:
                triplets, _ = sample_without_replacement_with_coloring(pool, args.count, indices)
        else:
            if with_replacement:
                triplets = sample_with_replacement_without_coloring(pool, args.count, rng)
            else:
                triplets, _ = sample_without_replacement_without_coloring(pool, args.count, rng)
        
        mode_str = f"{'WITH' if with_replacement else 'WITHOUT'} replacement, "
        mode_str += f"{'WITH' if args.coloring else 'WITHOUT'} coloring"
        print_triplets(triplets, mode_str)
    
    print()


if __name__ == "__main__":
    main()
