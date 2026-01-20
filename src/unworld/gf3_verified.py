"""
GF(3) Conservation - Python Implementation

Translated from GF3Conservation.dfy (formally verified in Dafny)
Maintains modulo 3 invariants for triadic operations.

Usage:
    from gf3_conservation import Trit, gf3_sum, is_balanced, balance_triad
"""

from enum import IntEnum
from typing import List, Tuple
from dataclasses import dataclass


# ===========================================================================
# GF(3) DATA TYPES
# ===========================================================================

class Trit(IntEnum):
    """GF(3) elements: -1, 0, +1"""
    MINUS = -1
    ZERO = 0
    PLUS = 1
    
    def __repr__(self) -> str:
        return {-1: "−", 0: "○", 1: "+"}[self.value]
    
    def __str__(self) -> str:
        return repr(self)


# ===========================================================================
# TRIT OPERATIONS
# ===========================================================================

def trit_value(t: Trit) -> int:
    """Extract integer value from Trit"""
    return t.value


def trit_from_int(n: int) -> Trit:
    """Convert integer to Trit (must be -1, 0, or 1)"""
    assert -1 <= n <= 1, f"trit_from_int requires -1 <= n <= 1, got {n}"
    return Trit(n)


# ===========================================================================
# GF(3) SUMMATION
# ===========================================================================

def gf3_sum(trits: List[Trit]) -> int:
    """Sum of trit values (recursive definition from Dafny)"""
    if len(trits) == 0:
        return 0
    return trit_value(trits[0]) + gf3_sum(trits[1:])


def gf3_sum_fast(trits: List[Trit]) -> int:
    """Optimized iterative sum"""
    return sum(t.value for t in trits)


# ===========================================================================
# CONSERVATION PREDICATES
# ===========================================================================

def gf3_conserved(trits: List[Trit]) -> bool:
    """Check if sequence satisfies GF(3) conservation"""
    return len(trits) == 0 or (gf3_sum_fast(trits) % 3 == 0)


def is_balanced(trits: List[Trit]) -> bool:
    """Check if sum ≡ 0 (mod 3)"""
    return gf3_sum_fast(trits) % 3 == 0


# ===========================================================================
# NORMALIZATION (Reduce to [-1, 0, 1])
# ===========================================================================

def normalize(n: int) -> int:
    """Normalize integer to GF(3) range [-1, 0, 1]"""
    mod3 = ((n % 3) + 3) % 3
    if mod3 == 0:
        return 0
    elif mod3 == 1:
        return 1
    else:
        return -1


# ===========================================================================
# ADDITION IN GF(3)
# ===========================================================================

def add_gf3(a: Trit, b: Trit) -> Trit:
    """Add two trits in GF(3)"""
    sum_val = trit_value(a) + trit_value(b)
    return trit_from_int(normalize(sum_val))


# ===========================================================================
# NEGATION IN GF(3)
# ===========================================================================

def negate_gf3(t: Trit) -> Trit:
    """Negate a trit: -(-1) = +1, -(0) = 0, -(+1) = -1"""
    return Trit(-t.value)


# ===========================================================================
# BALANCE A TRIAD
# ===========================================================================

def balance_triad(triad: List[Trit]) -> Trit:
    """Given 3 trits, compute the 4th trit that balances them"""
    assert len(triad) == 3, f"balance_triad requires exactly 3 trits, got {len(triad)}"
    
    s = gf3_sum_fast(triad)
    mod3 = (((-s) % 3) + 3) % 3
    
    if mod3 == 0:
        return Trit.ZERO
    elif mod3 == 1:
        return Trit.PLUS
    else:
        return Trit.MINUS


def compute_balancing_trit(triad: List[Trit]) -> Trit:
    """Alias for balance_triad (matches Dafny export)"""
    return balance_triad(triad)


# ===========================================================================
# QUAD BALANCING
# ===========================================================================

def is_quad_balanced(quad: List[Trit]) -> bool:
    """Check if a quad (4 trits) is balanced"""
    assert len(quad) == 4, f"is_quad_balanced requires exactly 4 trits, got {len(quad)}"
    return is_balanced(quad)


def make_balanced_quad(triad: List[Trit]) -> List[Trit]:
    """Create a balanced quad from a triad by adding the balancing trit"""
    assert len(triad) == 3
    balancing = balance_triad(triad)
    return triad + [balancing]


# ===========================================================================
# VERIFICATION (Lemma Equivalents)
# ===========================================================================

def verify_gf3_sum_associative(trits1: List[Trit], trits2: List[Trit]) -> bool:
    """Verify: GF3Sum(trits1 + trits2) == GF3Sum(trits1) + GF3Sum(trits2)"""
    combined = gf3_sum_fast(trits1 + trits2)
    separate = gf3_sum_fast(trits1) + gf3_sum_fast(trits2)
    return combined == separate


def verify_balanced_concatenation(trits1: List[Trit], trits2: List[Trit]) -> bool:
    """Verify: balanced(t1) ∧ balanced(t2) ⟹ balanced(t1 + t2)"""
    if not is_balanced(trits1) or not is_balanced(trits2):
        return True  # Precondition not met, vacuously true
    return is_balanced(trits1 + trits2)


def verify_balance_triad_correctness(triad: List[Trit]) -> bool:
    """Verify: triad + [balance_triad(triad)] is balanced"""
    if len(triad) != 3:
        return False
    quad = make_balanced_quad(triad)
    return is_balanced(quad)


def verify_gf3_conservation_theorem(trits: List[Trit]) -> bool:
    """
    Main theorem: If sequence length is multiple of 4 and each quad is balanced,
    then the entire sequence is balanced.
    """
    if len(trits) % 4 != 0:
        return True  # Precondition not met
    
    # Check each quad
    for i in range(len(trits) // 4):
        quad = trits[i*4:(i+1)*4]
        if not is_balanced(quad):
            return True  # Precondition not met
    
    # Verify conclusion
    return is_balanced(trits)


# ===========================================================================
# EXPORTED METHODS (Match Dafny Interface)
# ===========================================================================

def sum_trits(trits: List[Trit]) -> int:
    """Sum trit values (exported method)"""
    return gf3_sum_fast(trits)


def check_balanced(trits: List[Trit]) -> bool:
    """Check if sequence is balanced (exported method)"""
    return is_balanced(trits)


# ===========================================================================
# TESTING
# ===========================================================================

def test_basic_balance():
    """Test basic balancing operations"""
    # Test 1: [+1, +1, +1] needs -0 (sum=3, need 0 to balance)
    t1 = [Trit.PLUS, Trit.PLUS, Trit.PLUS]
    b1 = balance_triad(t1)
    assert is_balanced(t1 + [b1]), f"Failed: {t1} + [{b1}]"
    
    # Test 2: [+1, -1, 0] is already sum=0
    t2 = [Trit.PLUS, Trit.MINUS, Trit.ZERO]
    b2 = balance_triad(t2)
    assert is_balanced(t2 + [b2]), f"Failed: {t2} + [{b2}]"
    
    # Test 3: [-1, -1, +1] needs +1
    t3 = [Trit.MINUS, Trit.MINUS, Trit.PLUS]
    b3 = balance_triad(t3)
    assert is_balanced(t3 + [b3]), f"Failed: {t3} + [{b3}]"
    
    return True


def test_lemmas():
    """Verify lemma equivalents"""
    t1 = [Trit.PLUS, Trit.MINUS]
    t2 = [Trit.ZERO, Trit.PLUS, Trit.MINUS]
    
    assert verify_gf3_sum_associative(t1, t2), "Associativity failed"
    
    balanced1 = [Trit.PLUS, Trit.MINUS, Trit.ZERO]
    balanced2 = [Trit.PLUS, Trit.PLUS, Trit.PLUS, Trit.ZERO]  # sum=3, balanced
    assert verify_balanced_concatenation(balanced1, balanced2), "Concatenation failed"
    
    for _ in range(100):
        import random
        triad = [Trit(random.choice([-1, 0, 1])) for _ in range(3)]
        assert verify_balance_triad_correctness(triad), f"Triad correctness failed for {triad}"
    
    return True


def test_conservation_theorem():
    """Test the main conservation theorem"""
    # Build sequence of balanced quads
    quads = []
    for _ in range(10):
        import random
        triad = [Trit(random.choice([-1, 0, 1])) for _ in range(3)]
        quad = make_balanced_quad(triad)
        quads.extend(quad)
    
    assert verify_gf3_conservation_theorem(quads), "Conservation theorem failed"
    assert is_balanced(quads), "Full sequence not balanced"
    
    return True


def main():
    """Run tests (matches Dafny Main)"""
    print("GF(3) Conservation Module - Python Implementation")
    print("=" * 50)
    
    # Test 1: Balance [+1, +1, -1]
    triad1 = [Trit.PLUS, Trit.PLUS, Trit.MINUS]
    bal1 = balance_triad(triad1)
    check1 = check_balanced(triad1 + [bal1])
    print(f"Test 1: [+, +, −] + [{bal1}] => Balanced: {check1}")
    
    # Test 2: Balance [+1, 0, -1]
    triad2 = [Trit.PLUS, Trit.ZERO, Trit.MINUS]
    bal2 = balance_triad(triad2)
    check2 = check_balanced(triad2 + [bal2])
    print(f"Test 2: [+, ○, −] + [{bal2}] => Balanced: {check2}")
    
    # Test 3: Balance [+1, +1, +1]
    triad3 = [Trit.PLUS, Trit.PLUS, Trit.PLUS]
    bal3 = balance_triad(triad3)
    check3 = check_balanced(triad3 + [bal3])
    print(f"Test 3: [+, +, +] + [{bal3}] => Balanced: {check3}")
    
    print()
    print("Running verification tests...")
    assert test_basic_balance(), "Basic balance tests failed"
    print("✓ Basic balance tests passed")
    
    assert test_lemmas(), "Lemma tests failed"
    print("✓ Lemma verification passed")
    
    assert test_conservation_theorem(), "Conservation theorem test failed"
    print("✓ Conservation theorem verified")
    
    print()
    print("All tests passed! GF(3) conservation verified.")


if __name__ == "__main__":
    main()
