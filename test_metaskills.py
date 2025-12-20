#!/usr/bin/env python3
"""
TEST SUITE FOR METASKILLS

Comprehensive testing of FILTER, ITERATE, and INTEGRATE metaskills.

Run with: python test_metaskills.py
Or with uv: uv run test_metaskills.py
"""

import sys
import math
from typing import List, Any
from metaskills import (
    FilteringSystem, FilteringResult,
    IterationSystem, IterationResult,
    IntegrationSystem, IntegrationResult,
    measure_coherence, measure_entropy, satisfies_constraint
)


# ============================================================================
# TEST DATA
# ============================================================================

# Sample conversation history entries (simplified version of 720-entry dataset)
SAMPLE_ENTRIES = [
    # Duck entries (high signal)
    {"id": 1, "text": "duck: constraint satisfaction in learning", "theme": "learning"},
    {"id": 2, "text": "duck: time travel and reversibility", "theme": "temporal"},
    {"id": 3, "text": "duck: how coherence drives systems", "theme": "metaskills"},
    {"id": 4, "text": "duck: strange loops and self-reference", "theme": "consciousness"},
    {"id": 5, "text": "duck: filtering signal from noise", "theme": "methods"},

    # Non-duck entries (noise)
    {"id": 6, "text": "random thought about weather", "theme": "misc"},
    {"id": 7, "text": "what's for lunch today?", "theme": "misc"},
    {"id": 8, "text": "reminder to check email", "theme": "misc"},
    {"id": 9, "text": "thought about unrelated topic", "theme": "misc"},
    {"id": 10, "text": "another random comment", "theme": "misc"},

    # Semi-relevant entries (partial signal)
    {"id": 11, "text": "learning and iteration cycles", "theme": "learning"},
    {"id": 12, "text": "making connections between ideas", "theme": "integration"},
    {"id": 13, "text": "understanding requires multiple passes", "theme": "methods"},
    {"id": 14, "text": "systems that reflect on themselves", "theme": "consciousness"},
    {"id": 15, "text": "something about efficiency in processing", "theme": "methods"},
]


# ============================================================================
# TEST UTILITIES
# ============================================================================

class TestResults:
    """Track test results"""
    def __init__(self):
        self.passed = 0
        self.failed = 0
        self.tests = []

    def assert_true(self, condition: bool, message: str):
        """Assert a condition is true"""
        if condition:
            self.passed += 1
            self.tests.append(("PASS", message))
            return True
        else:
            self.failed += 1
            self.tests.append(("FAIL", message))
            return False

    def assert_equal(self, actual: Any, expected: Any, message: str):
        """Assert equality"""
        if actual == expected:
            self.passed += 1
            self.tests.append(("PASS", f"{message} (expected {expected})"))
            return True
        else:
            self.failed += 1
            self.tests.append(("FAIL", f"{message} (expected {expected}, got {actual})"))
            return False

    def assert_greater(self, actual: float, minimum: float, message: str):
        """Assert actual > minimum"""
        if actual > minimum:
            self.passed += 1
            self.tests.append(("PASS", f"{message} ({actual:.3f} > {minimum:.3f})"))
            return True
        else:
            self.failed += 1
            self.tests.append(("FAIL", f"{message} ({actual:.3f} not > {minimum:.3f})"))
            return False

    def assert_less(self, actual: float, maximum: float, message: str):
        """Assert actual < maximum"""
        if actual < maximum:
            self.passed += 1
            self.tests.append(("PASS", f"{message} ({actual:.3f} < {maximum:.3f})"))
            return True
        else:
            self.failed += 1
            self.tests.append(("FAIL", f"{message} ({actual:.3f} not < {maximum:.3f})"))
            return False

    def summary(self) -> str:
        """Print summary"""
        total = self.passed + self.failed
        percentage = 100.0 * self.passed / max(1, total)

        lines = [
            f"\n{'═' * 70}",
            f"TEST RESULTS: {self.passed}/{total} passed ({percentage:.1f}%)",
            f"{'═' * 70}"
        ]

        # Show failures first
        failures = [t for t in self.tests if t[0] == "FAIL"]
        if failures:
            lines.append("\nFAILURES:")
            for status, msg in failures:
                lines.append(f"  ✗ {msg}")

        # Show summary of passes
        lines.append(f"\n✓ {self.passed} tests passed")
        if self.failed > 0:
            lines.append(f"✗ {self.failed} tests failed")

        return "\n".join(lines)


# ============================================================================
# UTILITY TESTS
# ============================================================================

def test_utility_functions():
    """Test utility functions"""
    print("\n" + "─" * 70)
    print("TEST SUITE 1: UTILITY FUNCTIONS")
    print("─" * 70)

    results = TestResults()

    # Test coherence measurement
    high_coherence_data = [
        "duck: topic 1",
        "duck: topic 2",
        "duck: topic 3",
    ]
    low_coherence_data = [
        "duck: topic 1",
        "random: unrelated",
        "cat: something else",
    ]

    high_coh = measure_coherence(high_coherence_data)
    low_coh = measure_coherence(low_coherence_data)

    results.assert_greater(
        high_coh, low_coh,
        "Coherence: uniform data higher than mixed"
    )

    # Test entropy measurement
    high_entropy_data = ["a", "b", "c", "d", "e"]  # All unique
    low_entropy_data = ["a", "a", "a", "a", "a"]   # All same

    high_ent = measure_entropy(high_entropy_data)
    low_ent = measure_entropy(low_entropy_data)

    results.assert_greater(
        high_ent, low_ent,
        "Entropy: diverse data higher than uniform"
    )

    # Test constraint satisfaction
    item = {"text": "duck: topic", "theme": "learning"}

    results.assert_true(
        satisfies_constraint(item, "duck"),
        "Constraint: keyword matching"
    )

    results.assert_true(
        satisfies_constraint(item, ("theme", "learning")),
        "Constraint: field-value matching"
    )

    results.assert_true(
        satisfies_constraint(item, lambda x: "duck" in x.get("text", "")),
        "Constraint: function constraint"
    )

    print(results.summary())
    return results


# ============================================================================
# FILTERING TESTS
# ============================================================================

def test_filtering():
    """Test FILTERING metaskill"""
    print("\n" + "─" * 70)
    print("TEST SUITE 2: FILTERING METASKILL")
    print("─" * 70)

    results = TestResults()
    filter_system = FilteringSystem()

    # Test 1: Basic filtering
    print("\n  Test 1: Basic filtering with keyword constraint...")
    result = filter_system.apply(
        SAMPLE_ENTRIES,
        ["duck"],
        verbose=False
    )

    results.assert_greater(
        len(result.filtered_items), 0,
        "Filter: Found duck entries"
    )

    results.assert_less(
        len(result.filtered_items), len(SAMPLE_ENTRIES),
        "Filter: Filtered out non-duck entries"
    )

    # Test 2: Coherence improvement
    print("  Test 2: Coherence improvement...")
    results.assert_greater(
        result.filtered_coherence, result.original_coherence,
        "Filter: Output coherence > input coherence"
    )

    # Test 3: Multiple constraints
    print("  Test 3: Multiple constraints...")
    multi_result = filter_system.apply(
        SAMPLE_ENTRIES,
        [
            "duck",
            lambda x: len(x.get("text", "")) > 15  # Substantial entries
        ],
        verbose=False
    )

    results.assert_less(
        len(multi_result.filtered_items), len(result.filtered_items),
        "Filter: More constraints reduce results"
    )

    # Test 4: Compression ratio
    print("  Test 4: Compression ratio...")
    compression = result.filtered_count / result.original_count
    results.assert_greater(
        compression, 0.0,
        f"Filter: Positive compression ({compression:.1%} kept)"
    )
    results.assert_less(
        compression, 1.0,
        f"Filter: Not 100% compression"
    )

    # Test 5: Result structure
    print("  Test 5: Result structure...")
    results.assert_true(
        isinstance(result, FilteringResult),
        "Filter: Returns FilteringResult"
    )

    results.assert_true(
        hasattr(result, 'filtered_items'),
        "Filter: Result has filtered_items"
    )

    results.assert_true(
        hasattr(result, 'coherence_improvement'),
        "Filter: Result has coherence_improvement"
    )

    print(result.summary())
    print(results.summary())
    return results


# ============================================================================
# ITERATION TESTS
# ============================================================================

def test_iteration():
    """Test ITERATION metaskill"""
    print("\n" + "─" * 70)
    print("TEST SUITE 3: ITERATION METASKILL")
    print("─" * 70)

    results = TestResults()
    iterate_system = IterationSystem()

    # Test 1: Basic iteration
    print("\n  Test 1: Basic iteration...")
    iter_result = iterate_system.apply(
        SAMPLE_ENTRIES,
        num_cycles=3,
        verbose=False
    )

    results.assert_true(
        isinstance(iter_result, IterationResult),
        "Iterate: Returns IterationResult"
    )

    # Test 2: Cycle execution
    print("  Test 2: Cycle execution...")
    results.assert_equal(
        len(iter_result.cycles), 3,
        "Iterate: Completed all cycles"
    )

    # Test 3: Each cycle has output
    print("  Test 3: Cycle structure...")
    all_have_output = all(
        hasattr(cycle, 'output_state') for cycle in iter_result.cycles
    )
    results.assert_true(
        all_have_output,
        "Iterate: All cycles have output"
    )

    # Test 4: Patterns found
    print("  Test 4: Pattern discovery...")
    all_have_patterns = all(
        len(cycle.patterns_found) > 0 for cycle in iter_result.cycles
    )
    results.assert_true(
        all_have_patterns,
        "Iterate: Patterns found in each cycle"
    )

    # Test 5: Questions asked
    print("  Test 5: Question generation...")
    all_have_questions = all(
        len(cycle.questions_asked) > 0 for cycle in iter_result.cycles
    )
    results.assert_true(
        all_have_questions,
        "Iterate: Questions asked in each cycle"
    )

    # Test 6: Insights generated
    print("  Test 6: Meta-insight generation...")
    all_have_insights = all(
        len(cycle.meta_insights) > 0 for cycle in iter_result.cycles
    )
    results.assert_true(
        all_have_insights,
        "Iterate: Meta-insights generated"
    )

    # Test 7: Convergence checking
    print("  Test 7: Convergence detection...")
    converge_result = iterate_system.apply(
        SAMPLE_ENTRIES,
        num_cycles=5,
        max_iterations=10,
        verbose=False
    )

    results.assert_true(
        isinstance(converge_result.converged, bool),
        "Iterate: Convergence status tracked"
    )

    print(iter_result.summary())
    print(results.summary())
    return results


# ============================================================================
# INTEGRATION TESTS
# ============================================================================

def test_integration():
    """Test INTEGRATION metaskill"""
    print("\n" + "─" * 70)
    print("TEST SUITE 4: INTEGRATION METASKILL")
    print("─" * 70)

    results = TestResults()
    integrate_system = IntegrationSystem()

    # Define domains
    domain_learning = {
        "name": "learning",
        "description": "Learning systems with constraint satisfaction"
    }
    domain_consciousness = {
        "name": "consciousness",
        "description": "Consciousness as strange loops"
    }
    domain_computation = {
        "name": "computation",
        "description": "Computation as constraint satisfaction"
    }

    # Test 1: Basic integration
    print("\n  Test 1: Basic integration...")
    int_result = integrate_system.apply(
        [domain_learning, domain_consciousness, domain_computation],
        verbose=False
    )

    results.assert_true(
        isinstance(int_result, IntegrationResult),
        "Integrate: Returns IntegrationResult"
    )

    # Test 2: Domain preservation
    print("  Test 2: Domain preservation...")
    results.assert_equal(
        len(int_result.domains), 3,
        "Integrate: All domains included"
    )

    # Test 3: Isomorphisms found
    print("  Test 3: Isomorphism discovery...")
    results.assert_true(
        len(int_result.isomorphisms) > 0,
        "Integrate: Isomorphisms discovered"
    )

    # Test 4: Bridges built
    print("  Test 4: Bridge construction...")
    results.assert_true(
        len(int_result.bridges) > 0,
        "Integrate: Bridges built between domains"
    )

    # Test 5: Coherence preserved
    print("  Test 5: Coherence verification...")
    results.assert_true(
        int_result.coherence_preserved,
        "Integrate: Coherence preserved"
    )

    # Test 6: Emergent properties
    print("  Test 6: Emergent properties...")
    results.assert_true(
        len(int_result.emergent_properties) > 0,
        "Integrate: Emergent properties identified"
    )

    # Test 7: Integration result structure
    print("  Test 7: Result structure...")
    results.assert_true(
        hasattr(int_result, 'integrated_system'),
        "Integrate: Has integrated_system"
    )

    results.assert_true(
        hasattr(int_result.integrated_system, 'bridges'),
        "Integrate: Integrated system has bridges"
    )

    print(int_result.summary())
    print(results.summary())
    return results


# ============================================================================
# INTEGRATION TESTS (CHAINING METASKILLS)
# ============================================================================

def test_metaskill_chaining():
    """Test applying metaskills in sequence"""
    print("\n" + "─" * 70)
    print("TEST SUITE 5: METASKILL CHAINING")
    print("─" * 70)

    results = TestResults()

    # Chain: FILTER → ITERATE → INTEGRATE
    print("\n  Chaining: FILTER → ITERATE → INTEGRATE")

    # Step 1: FILTER
    print("\n  Step 1: Applying FILTER...")
    filter_system = FilteringSystem()
    filtered = filter_system.apply(
        SAMPLE_ENTRIES,
        ["duck"],
        verbose=False
    )

    results.assert_greater(
        filtered.coherence_improvement, 1.0,
        "Chain Step 1: FILTER improves coherence"
    )

    # Step 2: ITERATE on filtered results
    print("  Step 2: Applying ITERATE on filtered results...")
    iterate_system = IterationSystem()
    iterated = iterate_system.apply(
        filtered.filtered_items,
        num_cycles=2,
        verbose=False
    )

    results.assert_equal(
        len(iterated.cycles), 2,
        "Chain Step 2: ITERATE completed"
    )

    # Step 3: INTEGRATE (treating filtered items as domain)
    print("  Step 3: Applying INTEGRATE...")
    integrate_system = IntegrationSystem()
    integrated = integrate_system.apply(
        [filtered.filtered_items, iterated.cycles],
        verbose=False
    )

    results.assert_true(
        integrated.coherence_preserved,
        "Chain Step 3: INTEGRATE preserves coherence"
    )

    print("\n✓ Metaskill chaining successful")
    print(results.summary())
    return results


# ============================================================================
# MAIN TEST RUNNER
# ============================================================================

def run_all_tests():
    """Run all test suites"""
    print("\n" + "╔" + "=" * 68 + "╗")
    print("║" + "METASKILL TEST SUITE".center(68) + "║")
    print("║" + "Testing FILTER, ITERATE, INTEGRATE".center(68) + "║")
    print("╚" + "=" * 68 + "╝")

    all_results = []

    # Run all test suites
    all_results.append(("Utilities", test_utility_functions()))
    all_results.append(("Filtering", test_filtering()))
    all_results.append(("Iteration", test_iteration()))
    all_results.append(("Integration", test_integration()))
    all_results.append(("Chaining", test_metaskill_chaining()))

    # Final summary
    print("\n" + "=" * 70)
    print("FINAL TEST SUMMARY")
    print("=" * 70)

    total_passed = 0
    total_failed = 0

    for suite_name, result in all_results:
        total_passed += result.passed
        total_failed += result.failed
        status = "✓" if result.failed == 0 else "✗"
        print(f"{status} {suite_name:20} {result.passed:3}/{result.passed + result.failed:3} passed")

    total_tests = total_passed + total_failed
    percentage = 100.0 * total_passed / max(1, total_tests)

    print(f"\n{'─' * 70}")
    print(f"TOTAL: {total_passed}/{total_tests} tests passed ({percentage:.1f}%)")
    print(f"{'=' * 70}")

    if total_failed == 0:
        print("\n✓ ALL TESTS PASSED - METASKILL SYSTEM FUNCTIONAL")
        return 0
    else:
        print(f"\n✗ {total_failed} TESTS FAILED - REVIEW ABOVE")
        return 1


if __name__ == '__main__':
    exit_code = run_all_tests()
    sys.exit(exit_code)
