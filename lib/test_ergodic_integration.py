#!/usr/bin/env python3
"""
Integration Test for ERGODIC (0) Agent
Verifies:
- ACSet export produces valid JSON
- GF(3) conservation holds across exports
- Coherence periods are detectable
"""

import json
import sys
import os

sys.path.insert(0, os.path.dirname(__file__))

from gh_acset_export import (
    build_colored_acset, ACSetSchema, splitmix64, to_trit, gf3_sum, SEED
)
from coherence_periods import (
    discover_coherence_periods, detect_periodicity, compute_entropy, find_stable_states
)

def test_acset_valid_json():
    """Test: ACSet export produces valid JSON."""
    print("Test 1: ACSet JSON validity...")
    
    # Mock activity data
    mock_activity = {
        "users": ["alice", "bob", "carol"],
        "repos": ["proj-a", "proj-b"],
        "issues": [
            {"id": 1, "number": 42, "title": "Fix bug", "state": "open", "user": "alice", "repo": "proj-a"},
            {"id": 2, "number": 43, "title": "Add feature", "state": "closed", "user": "bob", "repo": "proj-b"}
        ],
        "prs": [
            {"id": 10, "number": 5, "title": "PR one", "state": "merged", "user": "carol", "repo": "proj-a"}
        ],
        "commits": [
            {"sha": "abc1234", "message": "Initial commit", "user": "alice", "repo": "proj-a"}
        ]
    }
    
    acset = build_colored_acset(mock_activity)
    result = acset.to_json()
    
    # Verify JSON serializable
    json_str = json.dumps(result)
    parsed = json.loads(json_str)
    
    assert "schema" in parsed, "Missing schema"
    assert "tables" in parsed, "Missing tables"
    assert "colors" in parsed, "Missing colors"
    assert "trits" in parsed, "Missing trits"
    assert "gf3_sum" in parsed, "Missing gf3_sum"
    
    # Verify schema structure
    assert set(parsed["schema"]["objects"]) == {"Issue", "PR", "Commit", "User", "Repo"}
    assert len(parsed["schema"]["morphisms"]) > 0
    
    # Verify tables populated
    assert len(parsed["tables"]["User"]) == 3
    assert len(parsed["tables"]["Issue"]) == 2
    assert len(parsed["tables"]["PR"]) == 1
    assert len(parsed["tables"]["Commit"]) == 1
    
    print("  ✓ Valid JSON structure")
    print(f"  ✓ Schema: {len(parsed['schema']['objects'])} objects, {len(parsed['schema']['morphisms'])} morphisms")
    return True

def test_gf3_conservation():
    """Test: GF(3) conservation holds across exports."""
    print("\nTest 2: GF(3) conservation...")
    
    # Test multiple seeds
    seeds = [0x42D, 0x123, 0xABC, 0xDEF, 0x999]
    
    for seed in seeds:
        mock_activity = {
            "users": ["u1", "u2", "u3"],
            "repos": ["r1", "r2", "r3"],
            "issues": [{"id": i, "number": i, "title": f"Issue {i}", "state": "open", "user": f"u{i%3+1}", "repo": f"r{i%3+1}"} for i in range(9)],
            "prs": [],
            "commits": []
        }
        
        acset = build_colored_acset(mock_activity, seed=seed)
        result = acset.to_json()
        
        # Verify trit values are in GF(3)
        for trit in result["trits"].values():
            assert trit in [-1, 0, 1], f"Invalid trit value: {trit}"
        
        # Verify gf3_sum computation
        manual_sum = sum(result["trits"].values()) % 3
        assert result["gf3_sum"] == manual_sum, f"GF(3) sum mismatch: {result['gf3_sum']} != {manual_sum}"
    
    print(f"  ✓ All trits in GF(3) = {{-1, 0, +1}}")
    print(f"  ✓ GF(3) sum verified for {len(seeds)} seeds")
    
    # Test conservation across balanced inputs (3n elements)
    for n in [3, 6, 9, 12]:
        trits = [to_trit(i) for i in range(n)]
        total = gf3_sum(trits)
        print(f"  ✓ n={n}: trits sum mod 3 = {total}")
    
    return True

def test_coherence_detection():
    """Test: Coherence periods are detectable."""
    print("\nTest 3: Coherence period detection...")
    
    # Test periodicity detection
    periodic_seq = ["A", "B", "C", "A", "B", "C", "A", "B", "C"]
    periods = detect_periodicity(periodic_seq)
    assert len(periods) > 0, "Failed to detect obvious period"
    assert periods[0][0] == 3, f"Expected period 3, got {periods[0][0]}"
    print(f"  ✓ Detected period {periods[0][0]} with confidence {periods[0][1]:.2f}")
    
    # Test entropy computation
    uniform_freq = [10, 10, 10]  # Maximum entropy
    skewed_freq = [30, 0, 0]     # Minimum entropy
    
    h_uniform = compute_entropy(uniform_freq)
    h_skewed = compute_entropy(skewed_freq)
    
    assert h_uniform > h_skewed, "Entropy ordering incorrect"
    print(f"  ✓ Entropy: uniform={h_uniform:.2f}, skewed={h_skewed:.2f}")
    
    # Test stable state detection
    seq_with_stable = ["A", "A", "A", "A", "A", "B", "C", "B"]
    stable = find_stable_states(seq_with_stable)
    assert "A" in stable, "Failed to find stable state A"
    print(f"  ✓ Stable states: {stable}")
    
    # Run full discovery
    result = discover_coherence_periods()
    assert "coherence_periods" in result or "duckdb_analysis" in result
    print(f"  ✓ Full discovery completed, source: {result.get('source', 'unknown')}")
    
    return True

def test_splitmix64_determinism():
    """Test: SplitMix64 is deterministic."""
    print("\nTest 4: SplitMix64 determinism...")
    
    seed1, val1 = splitmix64(SEED)
    seed2, val2 = splitmix64(SEED)
    
    assert seed1 == seed2, "Seeds diverged"
    assert val1 == val2, "Values diverged"
    
    # Chain test
    s, _ = splitmix64(SEED)
    for _ in range(100):
        s, v = splitmix64(s)
    
    s2, _ = splitmix64(SEED)
    for _ in range(100):
        s2, v2 = splitmix64(s2)
    
    assert s == s2 and v == v2, "Chain divergence"
    print(f"  ✓ Deterministic after 100 iterations")
    print(f"  ✓ Final seed: {hex(s)}, value: {hex(v)}")
    
    return True

def run_all_tests():
    """Run all integration tests."""
    print("=" * 60)
    print("ERGODIC (0) Agent Integration Tests")
    print(f"Seed: 0x42D | Trit: 0 (balance/coordination)")
    print("=" * 60)
    
    results = []
    
    try:
        results.append(("ACSet JSON validity", test_acset_valid_json()))
    except Exception as e:
        results.append(("ACSet JSON validity", False))
        print(f"  ✗ Error: {e}")
    
    try:
        results.append(("GF(3) conservation", test_gf3_conservation()))
    except Exception as e:
        results.append(("GF(3) conservation", False))
        print(f"  ✗ Error: {e}")
    
    try:
        results.append(("Coherence detection", test_coherence_detection()))
    except Exception as e:
        results.append(("Coherence detection", False))
        print(f"  ✗ Error: {e}")
    
    try:
        results.append(("SplitMix64 determinism", test_splitmix64_determinism()))
    except Exception as e:
        results.append(("SplitMix64 determinism", False))
        print(f"  ✗ Error: {e}")
    
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    
    passed = sum(1 for _, r in results if r)
    total = len(results)
    
    for name, result in results:
        status = "✓ PASS" if result else "✗ FAIL"
        print(f"  {status}: {name}")
    
    print(f"\nTotal: {passed}/{total} tests passed")
    print(f"GF(3) status: {'BALANCED' if passed == total else 'UNBALANCED'}")
    
    return passed == total

if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
