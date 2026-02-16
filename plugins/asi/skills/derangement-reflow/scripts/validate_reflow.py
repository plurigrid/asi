#!/usr/bin/env python3
"""
Derangement Reflow Validator
============================

Validates that skill triplets follow derangement constraints:
- No fixed points: σ(i) ≠ i
- GF(3) conservation: Σ trits ≡ 0 (mod 3)
- Tropical optimality: minimize path cost

Uses min-plus semiring for tropical geometry of interaction.
"""

import sys
import json
import hashlib
from dataclasses import dataclass, field
from typing import List, Tuple, Optional
from pathlib import Path


# SplitMix64 constants for deterministic coloring
GOLDEN = 0x9E3779B97F4A7C15
MIX1 = 0xBF58476D1CE4E5B9
MIX2 = 0x94D049BB133111EB

def splitmix64(state: int) -> int:
    """SplitMix64 PRNG step."""
    z = (state + GOLDEN) & 0xFFFFFFFFFFFFFFFF
    z = ((z ^ (z >> 30)) * MIX1) & 0xFFFFFFFFFFFFFFFF
    z = ((z ^ (z >> 27)) * MIX2) & 0xFFFFFFFFFFFFFFFF
    return (z ^ (z >> 31)) & 0xFFFFFFFFFFFFFFFF


def seed_to_trit(seed: int) -> int:
    """Convert seed to GF(3) trit via SplitMix64."""
    h = splitmix64(seed)
    return (h % 3) - 1  # Maps to {-1, 0, +1}


@dataclass
class Skill:
    """Skill with GF(3) trit assignment."""
    name: str
    trit: int
    color: str = ""
    role: str = ""
    
    def __post_init__(self):
        if not self.color:
            # Derive color from name hash
            h = int(hashlib.sha256(self.name.encode()).hexdigest()[:8], 16)
            self.color = f"#{splitmix64(h) & 0xFFFFFF:06X}"
        if not self.role:
            self.role = {-1: "VALIDATOR", 0: "COORDINATOR", 1: "GENERATOR"}.get(self.trit, "UNKNOWN")


@dataclass 
class ReflowResult:
    """Result of derangement reflow validation."""
    triplet: List[str]
    trits: List[int]
    gf3_conserved: bool
    derangement_valid: bool
    tropical_cost: float
    wev_extractable: bool
    violations: List[str] = field(default_factory=list)
    

def is_derangement(perm: List[int]) -> bool:
    """Check if permutation is a derangement (no fixed points)."""
    return all(p != i for i, p in enumerate(perm))


def tropical_distance(trits: List[int]) -> float:
    """
    Compute tropical (min-plus) distance for a skill path.
    
    In tropical geometry, optimal = minimum sum.
    Cost = Σ |trit_i - trit_{i+1}|
    
    Returns infinity if path has consecutive same-trit skills (fixed point).
    """
    if len(trits) < 2:
        return 0.0
    
    cost = 0.0
    for i in range(len(trits) - 1):
        if trits[i] == trits[i + 1]:
            return float('inf')  # Fixed point = invalid
        cost += abs(trits[i] - trits[i + 1])
    
    return cost


def validate_triplet(minus: Skill, ergodic: Skill, plus: Skill) -> ReflowResult:
    """
    Validate a GF(3) triplet for derangement reflow.
    
    Constraints:
    1. GF(3) conservation: sum ≡ 0 (mod 3)
    2. Derangement: no self-loops in information flow
    3. Tropical optimality: finite path cost
    """
    triplet = [minus.name, ergodic.name, plus.name]
    trits = [minus.trit, ergodic.trit, plus.trit]
    violations = []
    
    # GF(3) conservation
    trit_sum = sum(trits)
    gf3_conserved = (trit_sum % 3) == 0
    if not gf3_conserved:
        violations.append(f"GF(3) violation: sum={trit_sum}, mod 3 = {trit_sum % 3}")
    
    # Derangement check: all trits must be distinct for proper reflow
    unique_trits = len(set(trits))
    derangement_valid = unique_trits == 3  # All three roles present
    if not derangement_valid:
        violations.append(f"Derangement violation: only {unique_trits} unique trits")
    
    # Tropical cost
    tropical_cost = tropical_distance(trits)
    if tropical_cost == float('inf'):
        violations.append("Tropical violation: infinite path cost (fixed point)")
    
    # WEV extractable only if all constraints satisfied
    wev_extractable = gf3_conserved and derangement_valid and tropical_cost < float('inf')
    
    return ReflowResult(
        triplet=triplet,
        trits=trits,
        gf3_conserved=gf3_conserved,
        derangement_valid=derangement_valid,
        tropical_cost=tropical_cost,
        wev_extractable=wev_extractable,
        violations=violations
    )


def analyze_pr33_skills() -> dict:
    """
    Analyze PR #33's token-rent-validators for derangement issues.
    
    PR #33 adds: accept-no-substitutes, substitute-eraser, cheapskate
    All are VALIDATORS (-1).
    
    GitHub blind spot: Three validators with no generator interleaving
    creates fixed-point potential where validators validate validators.
    """
    # Skills from PR #33
    accept_no_substitutes = Skill("accept-no-substitutes", -1)
    substitute_eraser = Skill("substitute-eraser", -1)
    cheapskate = Skill("cheapskate", -1)
    
    # From PR body: these are the "balanced" skills
    skill_creator = Skill("skill-creator", 0)
    tree_sitter = Skill("tree-sitter", +1)
    chromatic_walk = Skill("chromatic-walk", +1)
    code_review = Skill("code-review", -1)
    narya_proofs = Skill("narya-proofs", -1)
    kolmogorov = Skill("kolmogorov-compression", +1)
    
    # Validate the claimed triplet
    pr_triplet = validate_triplet(accept_no_substitutes, skill_creator, tree_sitter)
    
    # Check for validator clustering (derangement violation)
    all_validators = [accept_no_substitutes, code_review, narya_proofs, 
                      substitute_eraser, cheapskate]
    
    validator_cluster_issue = {
        "issue": "Five validators can form self-validating clusters",
        "validators": [v.name for v in all_validators],
        "fix": "Interleave each validator pair with generator/coordinator",
        "recommended_triplets": [
            f"{v.name} (−1) ⊗ skill-creator (0) ⊗ tree-sitter (+1)"
            for v in all_validators[:3]
        ]
    }
    
    return {
        "pr_triplet_validation": {
            "triplet": pr_triplet.triplet,
            "trits": pr_triplet.trits,
            "gf3_conserved": pr_triplet.gf3_conserved,
            "derangement_valid": pr_triplet.derangement_valid,
            "tropical_cost": pr_triplet.tropical_cost,
            "wev_extractable": pr_triplet.wev_extractable,
            "violations": pr_triplet.violations
        },
        "missing_nuance": {
            "joint_world_modeling": "Validators lack shared world state with generators",
            "active_inference": "No free energy minimization across triplet",
            "task_interleaving": "Sequential validation without parallel MINUS/ERGODIC/PLUS dispatch"
        },
        "validator_cluster": validator_cluster_issue
    }


def main():
    """Run derangement reflow analysis."""
    print("╔══════════════════════════════════════════════════════════════════╗")
    print("║  DERANGEMENT REFLOW VALIDATOR                                    ║")
    print("║  World Operators as Information Reflow × Tropical Geometry       ║")
    print("╚══════════════════════════════════════════════════════════════════╝")
    print()
    
    analysis = analyze_pr33_skills()
    
    print("┌─ PR #33 TRIPLET VALIDATION ──────────────────────────────────────┐")
    triplet_result = analysis["pr_triplet_validation"]
    status = "✓" if triplet_result["wev_extractable"] else "⚠"
    print(f"│ Status: {status}")
    print(f"│ Triplet: {' ⊗ '.join(triplet_result['triplet'])}")
    print(f"│ Trits: {triplet_result['trits']} → sum={sum(triplet_result['trits'])}")
    print(f"│ GF(3) Conserved: {triplet_result['gf3_conserved']}")
    print(f"│ Derangement Valid: {triplet_result['derangement_valid']}")
    print(f"│ Tropical Cost: {triplet_result['tropical_cost']}")
    print(f"│ WEV Extractable: {triplet_result['wev_extractable']}")
    print("└──────────────────────────────────────────────────────────────────┘")
    print()
    
    print("┌─ MISSING NUANCE (GitHub Blind Spots) ────────────────────────────┐")
    for key, value in analysis["missing_nuance"].items():
        print(f"│ • {key}: {value}")
    print("└──────────────────────────────────────────────────────────────────┘")
    print()
    
    print("┌─ VALIDATOR CLUSTER ISSUE ────────────────────────────────────────┐")
    cluster = analysis["validator_cluster"]
    print(f"│ Issue: {cluster['issue']}")
    print(f"│ Validators: {', '.join(cluster['validators'])}")
    print(f"│ Fix: {cluster['fix']}")
    print("│ Recommended triplets:")
    for rec in cluster["recommended_triplets"]:
        print(f"│   • {rec}")
    print("└──────────────────────────────────────────────────────────────────┘")
    print()
    
    # Output JSON for programmatic use
    if "--json" in sys.argv:
        print(json.dumps(analysis, indent=2, default=str))
    
    # Exit with error if WEV not extractable
    return 0 if triplet_result["wev_extractable"] else 1


if __name__ == "__main__":
    sys.exit(main())
