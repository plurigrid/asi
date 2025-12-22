"""
Test: unworld Pattern Derivation
Duration: ~5 seconds
Status: Unit test for deterministic pattern generation
"""

import pytest


def simple_splitmix64(seed, index):
    """Simple SplitMix64 implementation for testing"""
    state = seed ^ index
    state += 0x9e3779b97f4a7c15
    z = state
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9
    z = (z ^ (z >> 27)) * 0x94d049bb133111eb
    return z ^ (z >> 31)


def color_at(seed, index):
    """Get deterministic color at index"""
    return simple_splitmix64(seed, index)


def gf3_trit(color):
    """Extract GF(3) trit from color"""
    remainder = color % 3
    # Map: 0 → -1, 1 → 0, 2 → +1
    return remainder - 1


class MockThreeMatch:
    """Mock three-match pattern for testing"""
    def __init__(self, genesis_seed, index):
        self.genesis_seed = genesis_seed
        self.index = index
        # Generate first two colors
        c1 = color_at(genesis_seed, index * 3)
        c2 = color_at(genesis_seed, index * 3 + 1)
        # Third color is chosen to ensure GF(3) balance
        c1_remainder = c1 % 3
        c2_remainder = c2 % 3
        c3_remainder = (3 - (c1_remainder + c2_remainder) % 3) % 3
        c3 = color_at(genesis_seed, index * 3 + 2)
        # Adjust c3 to match required remainder
        c3 = (c3 // 3) * 3 + c3_remainder

        self.colors = [c1, c2, c3]
        self.trits = [gf3_trit(c) for c in self.colors]

    def __eq__(self, other):
        return self.colors == other.colors

    def gf3_conserved(self):
        """Check if pattern conserves GF(3)"""
        return sum(self.trits) % 3 == 0


class MockUnworldChain:
    """Mock unworld pattern generator"""
    def __init__(self, genesis_seed):
        self.genesis_seed = genesis_seed

    def unworld_chain(self, depth=10, verify_gf3=True):
        """Generate pattern chain"""
        patterns = []
        for i in range(depth):
            pattern = MockThreeMatch(self.genesis_seed, i)
            if verify_gf3:
                assert pattern.gf3_conserved(), f"Pattern {i} not GF(3) conserved"
            patterns.append(pattern)
        return patterns


def test_determinism():
    """Test that same seed produces identical output"""
    genesis_seed = 0xDEADBEEF

    # Generate twice with same seed
    learner1 = MockUnworldChain(genesis_seed=genesis_seed)
    patterns1 = learner1.unworld_chain(depth=10, verify_gf3=True)

    learner2 = MockUnworldChain(genesis_seed=genesis_seed)
    patterns2 = learner2.unworld_chain(depth=10, verify_gf3=True)

    # Check lengths match
    assert len(patterns1) == len(patterns2)

    # Check each pattern is identical
    for i, (p1, p2) in enumerate(zip(patterns1, patterns2)):
        assert p1 == p2, f"Pattern {i} differs"


def test_different_seeds_different_patterns():
    """Test that different seeds produce different patterns"""
    seed1 = 0xDEADBEEF
    seed2 = 0xDEADBEEE

    learner1 = MockUnworldChain(genesis_seed=seed1)
    patterns1 = learner1.unworld_chain(depth=10, verify_gf3=True)

    learner2 = MockUnworldChain(genesis_seed=seed2)
    patterns2 = learner2.unworld_chain(depth=10, verify_gf3=True)

    # At least one pattern should differ
    any_different = False
    for p1, p2 in zip(patterns1, patterns2):
        if p1.colors != p2.colors:
            any_different = True
            break

    assert any_different, "Different seeds should produce different patterns"


def test_gf3_conservation_single_pattern():
    """Test that individual patterns conserve GF(3)"""
    genesis_seed = 0xDEADBEEF
    pattern = MockThreeMatch(genesis_seed, 0)

    # Sum of trits should be 0 mod 3
    assert pattern.gf3_conserved()


def test_gf3_conservation_chain():
    """Test that all patterns in chain conserve GF(3)"""
    genesis_seed = 0xDEADBEEF
    learner = MockUnworldChain(genesis_seed=genesis_seed)
    patterns = learner.unworld_chain(depth=100, verify_gf3=True)

    # All patterns should conserve GF(3)
    for i, pattern in enumerate(patterns):
        assert pattern.gf3_conserved(), f"Pattern {i} not GF(3) conserved"


def test_trit_distribution():
    """Test that trits are distributed"""
    genesis_seed = 0xDEADBEEF
    learner = MockUnworldChain(genesis_seed=genesis_seed)
    patterns = learner.unworld_chain(depth=100, verify_gf3=True)

    # Collect all trits
    all_trits = []
    for pattern in patterns:
        all_trits.extend(pattern.trits)

    # Count each trit
    counts = {-1: 0, 0: 0, 1: 0}
    for trit in all_trits:
        counts[trit] += 1

    # All should appear at least once (probabilistic but almost certain)
    assert counts[-1] > 0
    assert counts[0] > 0
    assert counts[1] > 0


def test_depth_parameter():
    """Test that depth parameter works"""
    genesis_seed = 0xDEADBEEF
    learner = MockUnworldChain(genesis_seed=genesis_seed)

    for depth in [1, 5, 10, 50, 100]:
        patterns = learner.unworld_chain(depth=depth, verify_gf3=True)
        assert len(patterns) == depth


def test_three_match_structure():
    """Test that three-match has correct structure"""
    genesis_seed = 0xDEADBEEF
    pattern = MockThreeMatch(genesis_seed, 0)

    # Should have exactly 3 colors
    assert len(pattern.colors) == 3

    # Should have exactly 3 trits
    assert len(pattern.trits) == 3

    # Each color should be a valid integer
    assert all(isinstance(c, int) for c in pattern.colors)

    # Each trit should be -1, 0, or +1
    assert all(t in [-1, 0, 1] for t in pattern.trits)


def test_color_determinism():
    """Test that color_at is deterministic"""
    seed = 0xDEADBEEF
    index = 42

    color1 = color_at(seed, index)
    color2 = color_at(seed, index)

    assert color1 == color2


def test_large_index_handling():
    """Test that large indices work"""
    seed = 0xDEADBEEF

    # Should handle large indices without error
    color1 = color_at(seed, 0)
    color2 = color_at(seed, 1000000)
    color3 = color_at(seed, 2**30)

    assert isinstance(color1, int)
    assert isinstance(color2, int)
    assert isinstance(color3, int)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
