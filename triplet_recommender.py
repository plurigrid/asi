#!/usr/bin/env python3
"""Skill Triplet Recommender - GF(3) Balanced Skill Allocation

Recommends valid skill triplets that satisfy GF(3) conservation:
    trit(MINUS) + trit(ERGODIC) + trit(PLUS) = -1 + 0 + 1 = 0 ≡ 0 (mod 3)

Usage:
    python triplet_recommender.py                    # Random triplets
    python triplet_recommender.py --theme category   # Themed triplets
    python triplet_recommender.py --skill foo        # Triplets containing foo
    python triplet_recommender.py --count 10         # Generate 10 triplets
"""

import re
import random
import argparse
from pathlib import Path
from collections import defaultdict
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional

# Seed for reproducibility
SEED = 0x6761795f636f6c6f  # "gay_colo"


@dataclass
class Skill:
    name: str
    trit: int  # -1, 0, or +1
    description: str = ""
    
    @property
    def trit_name(self) -> str:
        return {-1: "MINUS", 0: "ERGODIC", 1: "PLUS"}[self.trit]


@dataclass  
class Triplet:
    minus: Skill
    ergodic: Skill
    plus: Skill
    
    @property
    def conserved(self) -> bool:
        return (self.minus.trit + self.ergodic.trit + self.plus.trit) % 3 == 0
    
    def __str__(self) -> str:
        return f"{self.minus.name} (-1) ⊗ {self.ergodic.name} (0) ⊗ {self.plus.name} (+1) = 0 ✓"


def load_skills(skills_dir: Path) -> Dict[int, List[Skill]]:
    """Load all skills and categorize by trit."""
    trits = defaultdict(list)
    
    for skill_md in skills_dir.glob("*/SKILL.md"):
        name = skill_md.parent.name
        content = skill_md.read_text()
        
        # Extract trit
        match = re.search(r'trit:\s*([+-]?[01])', content)
        if match:
            trit = int(match.group(1))
        else:
            trit = 0  # Default to ERGODIC
        
        # Extract description
        desc_match = re.search(r'description:\s*["\']?([^"\'\n]+)', content)
        desc = desc_match.group(1) if desc_match else ""
        
        trits[trit].append(Skill(name, trit, desc))
    
    return trits


def recommend_random(skills: Dict[int, List[Skill]], count: int = 5, seed: Optional[int] = None) -> List[Triplet]:
    """Generate random valid triplets."""
    if seed is not None:
        random.seed(seed)
    
    minus = skills[-1]
    ergodic = skills[0]
    plus = skills[1]
    
    triplets = []
    for _ in range(count):
        m = random.choice(minus)
        e = random.choice(ergodic)
        p = random.choice(plus)
        triplets.append(Triplet(m, e, p))
    
    return triplets


def recommend_themed(skills: Dict[int, List[Skill]], theme: str) -> List[Triplet]:
    """Generate triplets matching a theme keyword."""
    theme_lower = theme.lower()
    
    def matches_theme(skill: Skill) -> bool:
        return theme_lower in skill.name.lower() or theme_lower in skill.description.lower()
    
    minus = [s for s in skills[-1] if matches_theme(s)]
    ergodic = [s for s in skills[0] if matches_theme(s)]
    plus = [s for s in skills[1] if matches_theme(s)]
    
    triplets = []
    
    # Generate all valid combinations
    for m in minus:
        for e in ergodic:
            for p in plus:
                triplets.append(Triplet(m, e, p))
    
    # If no themed triplets, try partial matches
    if not triplets:
        all_themed = [s for cat in skills.values() for s in cat if matches_theme(s)]
        if all_themed:
            print(f"Note: Found {len(all_themed)} skills matching '{theme}' but no complete triplets.")
            print("Showing triplets containing at least one matching skill:\n")
            
            for themed_skill in all_themed[:3]:
                if themed_skill.trit == -1:
                    e = random.choice(skills[0])
                    p = random.choice(skills[1])
                    triplets.append(Triplet(themed_skill, e, p))
                elif themed_skill.trit == 0:
                    m = random.choice(skills[-1])
                    p = random.choice(skills[1])
                    triplets.append(Triplet(m, themed_skill, p))
                else:
                    m = random.choice(skills[-1])
                    e = random.choice(skills[0])
                    triplets.append(Triplet(m, e, themed_skill))
    
    return triplets


def recommend_containing(skills: Dict[int, List[Skill]], skill_name: str) -> List[Triplet]:
    """Generate triplets containing a specific skill."""
    # Find the skill
    target = None
    for cat_skills in skills.values():
        for s in cat_skills:
            if s.name == skill_name or skill_name in s.name:
                target = s
                break
        if target:
            break
    
    if not target:
        print(f"Skill '{skill_name}' not found.")
        return []
    
    triplets = []
    
    if target.trit == -1:
        for e in skills[0]:
            for p in skills[1]:
                triplets.append(Triplet(target, e, p))
    elif target.trit == 0:
        for m in skills[-1]:
            for p in skills[1]:
                triplets.append(Triplet(m, target, p))
    else:
        for m in skills[-1]:
            for e in skills[0]:
                triplets.append(Triplet(m, e, target))
    
    return triplets


def print_stats(skills: Dict[int, List[Skill]]):
    """Print skill distribution statistics."""
    minus = len(skills[-1])
    ergodic = len(skills[0])
    plus = len(skills[1])
    total = minus + ergodic + plus
    
    print("=" * 60)
    print("SKILL DISTRIBUTION")
    print("=" * 60)
    print(f"MINUS (-1):   {minus:>3} skills")
    print(f"ERGODIC (0):  {ergodic:>3} skills")
    print(f"PLUS (+1):    {plus:>3} skills")
    print(f"Total:        {total:>3} skills")
    print()
    print(f"Possible triplets: {minus * ergodic * plus:,}")
    print(f"Sum: {-minus + plus} ≡ {(-minus + plus) % 3} (mod 3)")
    print("=" * 60)
    print()


def main():
    parser = argparse.ArgumentParser(description="Recommend GF(3)-balanced skill triplets")
    parser.add_argument("--theme", "-t", help="Filter by theme keyword")
    parser.add_argument("--skill", "-s", help="Include specific skill")
    parser.add_argument("--count", "-n", type=int, default=5, help="Number of triplets")
    parser.add_argument("--seed", type=int, default=SEED, help="Random seed")
    parser.add_argument("--stats", action="store_true", help="Show distribution stats")
    args = parser.parse_args()
    
    skills_dir = Path(__file__).parent / "skills"
    skills = load_skills(skills_dir)
    
    if args.stats:
        print_stats(skills)
        return
    
    print_stats(skills)
    
    if args.skill:
        print(f"Triplets containing '{args.skill}':")
        print("-" * 60)
        triplets = recommend_containing(skills, args.skill)
        for t in triplets[:args.count]:
            print(f"  {t}")
    elif args.theme:
        print(f"Themed triplets for '{args.theme}':")
        print("-" * 60)
        triplets = recommend_themed(skills, args.theme)
        for t in triplets[:args.count]:
            print(f"  {t}")
    else:
        print("Random valid triplets:")
        print("-" * 60)
        triplets = recommend_random(skills, args.count, args.seed)
        for t in triplets:
            print(f"  {t}")
    
    print()


if __name__ == "__main__":
    main()
