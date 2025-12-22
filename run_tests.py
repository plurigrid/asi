#!/usr/bin/env python3
"""
Plurigrid ASI Skills - Test Suite Runner

Runs all validation tests for the new skill ecosystem.
"""

import sys
import subprocess
import os
from pathlib import Path


def print_header(title):
    """Print formatted header"""
    print("\n" + "=" * 80)
    print(f"  {title}")
    print("=" * 80 + "\n")


def run_tests(test_filter=None, verbose=True):
    """Run pytest with given filter"""
    cmd = ["python", "-m", "pytest"]

    if test_filter:
        cmd.append(f"-k {test_filter}")

    if verbose:
        cmd.append("-v")

    cmd.append("tests/")

    return subprocess.run(cmd, cwd=str(Path(__file__).parent))


def main():
    """Main test runner"""
    test_dir = Path(__file__).parent / "tests"

    if not test_dir.exists():
        print("Error: tests/ directory not found")
        return 1

    print_header("PLURIGRID ASI SKILLS - TEST SUITE")
    print("Testing: langevin-dynamics, fokker-planck, unworld, paperproof")
    print("Status: All new skills + GF(3) conservation + integration tests")

    # Test categories
    test_suites = [
        ("Unit Tests", "test_langevin_basic or test_fokker_planck_basic or test_unworld_basic or test_paperproof_basic"),
        ("GF(3) Conservation Tests", "test_gf3_conservation"),
        ("Integration Tests", "test_integration"),
        ("All Tests", None)
    ]

    results = {}

    for suite_name, test_filter in test_suites[:-1]:  # Skip "All Tests" for now
        print_header(f"Running: {suite_name}")
        result = run_tests(test_filter=test_filter, verbose=True)
        results[suite_name] = result.returncode

    # Run all tests
    print_header("Running: All Tests Combined")
    result = run_tests(verbose=True)
    results["All Tests"] = result.returncode

    # Print summary
    print_header("TEST SUMMARY")

    passed = sum(1 for code in results.values() if code == 0)
    total = len(results)

    for suite_name, code in results.items():
        status = "✅ PASSED" if code == 0 else "❌ FAILED"
        print(f"{suite_name:.<50} {status}")

    print("\n" + "-" * 80)
    print(f"Results: {passed}/{total} test suites passed")
    print("-" * 80)

    return 0 if passed == total else 1


if __name__ == "__main__":
    sys.exit(main())
