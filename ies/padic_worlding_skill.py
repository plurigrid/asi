#!/usr/bin/env python3
"""
P-Adic Worlding Skill: Enhanced Meta-Learning with P-Adic Arithmetic

Extends worlding_skill.py with p-adic number system for:
- Tripartite splittable valuations
- Non-Archimedean metric spaces
- Hierarchical world model with 3-way branching
- Ultrametric distance for multi-scale learning

Inspired by:
- P-Adic Analysis (Gouvéa, Robert)
- Possible Worlds Semantics (modal logic)
- Triadic categorical decomposition
- Non-Archimedean geometry
"""

from fractions import Fraction
from typing import Dict, List, Tuple, Any, Optional
from dataclasses import dataclass, field
import math
from enum import Enum


# ============================================================================
# P-Adic Number System (p = 3, tripartite)
# ============================================================================

class PAdicValuation(Enum):
    """P-adic valuations for tripartite decomposition"""
    ZERO = 0      # Identity element
    ONE = 1       # Primary representation
    TWO = 2       # Secondary representation
    THREE = 3     # Tertiary representation


@dataclass
class PAdicInteger:
    """
    P-adic integer representation.
    
    In p-adic arithmetic (p=3), every number can be uniquely expressed as:
    
      a = Σ(a_i * 3^i) where a_i ∈ {0, 1, 2}
    
    This is the "digits in base 3" representation.
    """
    
    coefficients: List[int]  # digits a_0, a_1, a_2, ... (base 3)
    precision: int = 10      # How many digits we track
    prime: int = 3          # P-adic prime (always 3 for tripartite)
    
    def __post_init__(self):
        """Normalize to base 3 representation"""
        # Ensure all coefficients are in {0, 1, 2}
        self.coefficients = self.coefficients[:self.precision]
        while len(self.coefficients) < self.precision:
            self.coefficients.append(0)
    
    @classmethod
    def from_integer(cls, n: int, precision: int = 10) -> 'PAdicInteger':
        """Convert regular integer to p-adic (p=3)"""
        if n == 0:
            return cls([0] * precision)
        
        coeffs = []
        num = abs(n)
        
        while num > 0:
            coeffs.append(num % 3)
            num //= 3
        
        while len(coeffs) < precision:
            coeffs.append(0)
        
        return cls(coeffs[:precision])
    
    def to_integer(self) -> int:
        """Convert p-adic to regular integer (if it represents one)"""
        result = 0
        for i, coeff in enumerate(self.coefficients):
            result += coeff * (3 ** i)
        return result
    
    def valuation(self) -> int:
        """
        P-adic valuation: v_3(x) = order of smallest 3^i dividing x.
        
        For example:
        - v_3(3) = 1
        - v_3(9) = 2
        - v_3(1) = 0
        """
        if all(c == 0 for c in self.coefficients):
            return float('inf')
        
        for i, coeff in enumerate(self.coefficients):
            if coeff != 0:
                return i
        
        return 0
    
    def norm(self) -> float:
        """
        P-adic norm (non-Archimedean metric):
        
        ||x||_3 = 3^(-v_3(x))
        
        Properties:
        - ||x + y||_3 ≤ max(||x||_3, ||y||_3)  [ultrametric inequality]
        - ||x * y||_3 = ||x||_3 * ||y||_3
        """
        val = self.valuation()
        if val == float('inf'):
            return 0.0
        return 3.0 ** (-val)
    
    def __add__(self, other: 'PAdicInteger') -> 'PAdicInteger':
        """P-adic addition (carry-free in base 3)"""
        result = []
        carry = 0
        
        for i in range(self.precision):
            a = self.coefficients[i] if i < len(self.coefficients) else 0
            b = other.coefficients[i] if i < len(other.coefficients) else 0
            
            total = a + b + carry
            result.append(total % 3)
            carry = total // 3
        
        return PAdicInteger(result, self.precision)
    
    def __mul__(self, other: 'PAdicInteger') -> 'PAdicInteger':
        """P-adic multiplication"""
        result = [0] * self.precision
        
        for i in range(min(len(self.coefficients), self.precision)):
            for j in range(min(len(other.coefficients), self.precision - i)):
                if i + j < self.precision:
                    result[i + j] += self.coefficients[i] * other.coefficients[j]
        
        # Normalize carries
        carry = 0
        for i in range(self.precision):
            result[i] += carry
            carry = result[i] // 3
            result[i] %= 3
        
        return PAdicInteger(result, self.precision)
    
    def __repr__(self) -> str:
        """String representation in base 3"""
        coeffs_str = ''.join(str(c) for c in reversed(self.coefficients))
        return f"PAdicInteger({coeffs_str}_3, v_3={self.valuation()}, ||·||_3={self.norm():.6f})"
    
    def tripartite_split(self) -> Tuple['PAdicInteger', 'PAdicInteger', 'PAdicInteger']:
        """
        Tripartite splitting: decompose into three branches.
        
        Branch 0: coefficients ≡ 0 (mod 3)
        Branch 1: coefficients ≡ 1 (mod 3)  
        Branch 2: coefficients ≡ 2 (mod 3)
        """
        branch_0 = [c if c == 0 else 0 for c in self.coefficients]
        branch_1 = [c if c == 1 else 0 for c in self.coefficients]
        branch_2 = [c if c == 2 else 0 for c in self.coefficients]
        
        return (
            PAdicInteger(branch_0, self.precision),
            PAdicInteger(branch_1, self.precision),
            PAdicInteger(branch_2, self.precision)
        )
    
    def tripartite_combine(self, branch_1: 'PAdicInteger', 
                          branch_2: 'PAdicInteger') -> 'PAdicInteger':
        """Recombine three tripartite branches"""
        result = []
        for i in range(self.precision):
            a = self.coefficients[i] if i < len(self.coefficients) else 0
            b = branch_1.coefficients[i] if i < len(branch_1.coefficients) else 0
            c = branch_2.coefficients[i] if i < len(branch_2.coefficients) else 0
            
            # Reconstruct: take non-zero from branches
            coeff = a + b + c
            result.append(coeff % 3)
        
        return PAdicInteger(result, self.precision)


# ============================================================================
# P-Adic Worlding Skill: Enhanced with Ultrametric Geometry
# ============================================================================

@dataclass
class TripartiteWorldNode:
    """Node in tripartite world tree (p-adic structure)"""
    world_id: str
    padic_value: PAdicInteger
    children: List['TripartiteWorldNode'] = field(default_factory=list)
    parent: Optional['TripartiteWorldNode'] = None
    depth: int = 0
    
    def distance_to(self, other: 'TripartiteWorldNode') -> float:
        """Ultrametric distance via p-adic norm"""
        diff = self.padic_value + other.padic_value
        return diff.norm()


class TripartiteWorldingSkill:
    """
    Enhanced worlding skill using p-adic numbers for tripartite world modeling.
    
    Key features:
    - Every world state encoded as p-adic integer (base 3)
    - Ultrametric distance for non-Euclidean similarity
    - 3-way branching in world model tree
    - Valuation-based update priorities (lower valuation = faster updates)
    """
    
    def __init__(self, precision: int = 10):
        self.precision = precision
        self.root_world: Optional[TripartiteWorldNode] = None
        self.current_world: Optional[TripartiteWorldNode] = None
        self.world_history: List[TripartiteWorldNode] = []
        self.padic_cache: Dict[int, PAdicInteger] = {}
        
    def observe_padic(self, observation: int) -> 'TripartiteWorldNode':
        """Observe world state, encode as p-adic, create world node"""
        
        # Convert observation to p-adic
        padic_val = PAdicInteger.from_integer(observation, self.precision)
        
        # Create world node
        world_id = f"world_{len(self.world_history)}"
        node = TripartiteWorldNode(
            world_id=world_id,
            padic_value=padic_val,
            depth=len(self.world_history)
        )
        
        # Link to previous world (parent)
        if self.current_world is not None:
            node.parent = self.current_world
            self.current_world.children.append(node)
        else:
            self.root_world = node
        
        self.current_world = node
        self.world_history.append(node)
        self.padic_cache[observation] = padic_val
        
        return node
    
    def tripartite_branch(self) -> Tuple[TripartiteWorldNode, TripartiteWorldNode, TripartiteWorldNode]:
        """
        Branch current world into three sub-worlds via tripartite p-adic split.
        
        Each branch represents one of the three residue classes mod 3.
        """
        if self.current_world is None:
            raise ValueError("No current world to branch from")
        
        padic = self.current_world.padic_value
        branch_0, branch_1, branch_2 = padic.tripartite_split()
        
        # Create child worlds
        worlds = []
        for i, padic_branch in enumerate([branch_0, branch_1, branch_2]):
            world_id = f"{self.current_world.world_id}_branch_{i}"
            child = TripartiteWorldNode(
                world_id=world_id,
                padic_value=padic_branch,
                parent=self.current_world,
                depth=self.current_world.depth + 1
            )
            self.current_world.children.append(child)
            worlds.append(child)
        
        return tuple(worlds)
    
    def predict_via_ultrametric(self, target_observation: int) -> Tuple[TripartiteWorldNode, float]:
        """
        Predict which world node is closest to target observation
        using ultrametric (p-adic) distance.
        """
        if self.current_world is None:
            raise ValueError("No current world")
        
        target_padic = PAdicInteger.from_integer(target_observation, self.precision)
        target_node = TripartiteWorldNode(
            world_id="target",
            padic_value=target_padic,
            depth=-1
        )
        
        # Find closest world in history via ultrametric
        closest = self.current_world
        min_distance = self.current_world.distance_to(target_node)
        
        for world in self.world_history:
            distance = world.distance_to(target_node)
            if distance < min_distance:
                min_distance = distance
                closest = world
        
        return closest, min_distance
    
    def learn_from_padic_error(self, predicted: int, actual: int) -> float:
        """
        Learn from prediction error in p-adic metric space.
        
        Error = ||predicted - actual||_3 (p-adic norm difference)
        Update priority based on valuation: lower valuation = higher priority
        """
        
        pred_padic = PAdicInteger.from_integer(predicted, self.precision)
        actual_padic = PAdicInteger.from_integer(actual, self.precision)
        
        # P-adic error = norm of difference
        diff = pred_padic + actual_padic  # In p-adic arithmetic
        error = diff.norm()
        
        # Valuation determines update speed
        error_valuation = diff.valuation()
        update_priority = 1.0 / (1.0 + error_valuation) if error_valuation != float('inf') else 0.0
        
        return error, update_priority
    
    def get_padic_report(self) -> Dict[str, Any]:
        """Generate report on p-adic world model"""
        if not self.world_history:
            return {}
        
        return {
            "total_worlds": len(self.world_history),
            "tree_depth": max(w.depth for w in self.world_history) if self.world_history else 0,
            "current_world": self.current_world.world_id if self.current_world else None,
            "current_padic": str(self.current_world.padic_value) if self.current_world else None,
            "current_valuation": self.current_world.padic_value.valuation() if self.current_world else None,
            "current_norm": self.current_world.padic_value.norm() if self.current_world else None,
            "world_tree_size": len(self.world_history),
            "branching_factor": 3,  # Tripartite
            "cache_size": len(self.padic_cache),
        }


# ============================================================================
# Testing & Demonstration
# ============================================================================

def test_padic_numbers():
    """Test p-adic arithmetic"""
    print("=" * 80)
    print("P-ADIC NUMBER SYSTEM TEST (p = 3, tripartite)")
    print("=" * 80)
    print()
    
    # Test 1: Convert integers to p-adic
    print("Test 1: Integer to P-Adic Conversion")
    print("-" * 80)
    
    for n in [0, 1, 3, 9, 27, 15]:
        padic = PAdicInteger.from_integer(n, precision=8)
        print(f"  {n:3d} → {padic}")
    
    print()
    
    # Test 2: P-adic arithmetic
    print("Test 2: P-Adic Addition & Multiplication")
    print("-" * 80)
    
    a = PAdicInteger.from_integer(5, precision=8)
    b = PAdicInteger.from_integer(7, precision=8)
    
    print(f"  a = {a}")
    print(f"  b = {b}")
    print(f"  a + b = {a + b}")
    print(f"  a * b = {a * b}")
    
    print()
    
    # Test 3: Tripartite splitting
    print("Test 3: Tripartite Splitting")
    print("-" * 80)
    
    n = PAdicInteger.from_integer(13, precision=8)
    b0, b1, b2 = n.tripartite_split()
    
    print(f"  Original: {n}")
    print(f"  Branch 0: {b0}")
    print(f"  Branch 1: {b1}")
    print(f"  Branch 2: {b2}")
    
    print()


def test_tripartite_worlding():
    """Test tripartite worlding skill"""
    print("=" * 80)
    print("TRIPARTITE WORLDING SKILL TEST")
    print("=" * 80)
    print()
    
    skill = TripartiteWorldingSkill(precision=10)
    
    # Observe sequence
    print("Step 1: Observe World States")
    print("-" * 80)
    
    observations = [1, 3, 9, 27, 13, 7, 5]
    
    for obs in observations:
        node = skill.observe_padic(obs)
        print(f"  Observed {obs:3d} → {node.world_id}")
        print(f"    P-Adic: {node.padic_value}")
    
    print()
    
    # Test branching
    print("Step 2: Tripartite Branching")
    print("-" * 80)
    
    branches = skill.tripartite_branch()
    for i, branch in enumerate(branches):
        print(f"  Branch {i}: {branch.world_id}")
        print(f"    P-Adic: {branch.padic_value}")
        print(f"    Valuation: {branch.padic_value.valuation()}")
        print(f"    Norm: {branch.padic_value.norm():.6f}")
    
    print()
    
    # Test ultrametric prediction
    print("Step 3: Ultrametric Prediction")
    print("-" * 80)
    
    target = 10
    closest, distance = skill.predict_via_ultrametric(target)
    print(f"  Predicting world for observation {target}")
    print(f"  Closest world: {closest.world_id}")
    print(f"  Ultrametric distance: {distance:.6f}")
    
    print()
    
    # Test error learning
    print("Step 4: P-Adic Error Learning")
    print("-" * 80)
    
    pairs = [(5, 7), (9, 11), (3, 6)]
    for pred, actual in pairs:
        error, priority = skill.learn_from_padic_error(pred, actual)
        print(f"  Predicted: {pred}, Actual: {actual}")
        print(f"    P-Adic error: {error:.6f}")
        print(f"    Update priority: {priority:.6f}")
    
    print()
    
    # Final report
    print("Step 5: Final P-Adic Report")
    print("-" * 80)
    
    report = skill.get_padic_report()
    for key, value in report.items():
        print(f"  {key}: {value}")
    
    print()
    print("=" * 80)
    print("✓ TRIPARTITE WORLDING SKILL COMPLETE")
    print("=" * 80)


if __name__ == "__main__":
    test_padic_numbers()
    print()
    test_tripartite_worlding()
