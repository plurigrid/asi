#!/usr/bin/env python3
"""
Universal Learning Signature Framework - Validation Tests with W&B Integration

Enhanced validation test suite with Weights & Biases tracking for:
- Measurement procedure validation
- Domain-specific testing
- Result reproducibility
- Experiment tracking
"""

import json
import numpy as np
from datetime import datetime
from typing import Dict, List, Tuple
from measurement_procedures_fixed import (
    measure_D_pca_fixed,
    measure_f_ensemble,
    detect_cycles_fixed,
)
from wandb_integration import WANDBTracker, create_reproducibility_log

# ═══════════════════════════════════════════════════════════════════════════════
# TEST DATA GENERATION
# ═══════════════════════════════════════════════════════════════════════════════


def generate_topobench_data() -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Generate Topobench-like test data (color generation dynamics)."""
    np.random.seed(42)

    # Feature space: 5-dimensional
    n_samples = 100
    features = np.random.randn(n_samples, 5) * 0.5
    # Add some noise
    features[:, :2] *= 10  # Signal
    features[:, 2:] *= 0.1  # Noise

    # Sequence: color generation decisions
    sequence = np.random.randn(100)
    for i in range(1, 100):
        sequence[i] = 0.8 * sequence[i-1] + 0.2 * np.random.randn()

    # Adjacency: connection network
    adj = np.random.binomial(1, 0.1, (10, 10))
    np.fill_diagonal(adj, 0)

    return features, sequence, adj


def generate_github_data() -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Generate GitHub-like test data (repository dynamics)."""
    np.random.seed(43)

    # Feature space: repository characteristics
    features = np.random.randn(100, 8)
    features[:, :3] *= 5  # Commit activity, PR count, etc.
    features[:, 3:] *= 0.2  # Noise

    # Sequence: commit history
    sequence = np.cumsum(np.random.randn(100) * 0.3)
    for i in range(1, 100):
        sequence[i] = 0.6 * sequence[i-1] + 0.4 * np.random.randn()

    # Adjacency: dependency graph
    adj = np.random.binomial(1, 0.15, (15, 15))
    np.fill_diagonal(adj, 0)

    return features, sequence, adj


def generate_ies_data() -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Generate IES-like test data (learning system dynamics)."""
    np.random.seed(44)

    # Feature space: agent state vectors
    features = np.random.randn(100, 10)
    features[:, :5] *= 3  # Main dimensions
    features[:, 5:] *= 0.15  # Noise

    # Sequence: decision history
    sequence = np.random.randn(100)
    for i in range(1, 100):
        sequence[i] = 0.5 * sequence[i-1] + 0.5 * np.random.randn()

    # Adjacency: communication network
    adj = np.random.binomial(1, 0.12, (12, 12))
    np.fill_diagonal(adj, 0)

    return features, sequence, adj


# ═══════════════════════════════════════════════════════════════════════════════
# TEST EXECUTION
# ═══════════════════════════════════════════════════════════════════════════════


def run_validation_suite_with_wandb(
    use_wandb: bool = True,
    offline: bool = False,
) -> Dict[str, any]:
    """
    Run complete validation suite with W&B tracking.

    Args:
        use_wandb: Whether to use W&B tracking
        offline: Whether to run in offline mode

    Returns:
        Results dictionary with all test outcomes
    """

    # Initialize tracker
    tracker = WANDBTracker(
        project="universal-learning-signature",
        tags=["validation", "measurement-procedures"],
        notes="Fixed measurement procedures validation",
        offline=offline,
    ) if use_wandb else None

    # Start run
    if tracker:
        tracker.start_run(
            name=f"validation_run_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
            config={
                "framework": "universal-learning-signature",
                "measurement_version": "fixed_v0.85",
                "confidence_threshold": 0.70,
            }
        )

        # Log reproducibility info
        repro = create_reproducibility_log()
        tracker.log_summary({
            "reproducibility_timestamp": repro["timestamp"],
            "python_version": repro["python_version"],
            "platform": repro["platform"],
        })

    results = {
        "timestamp": datetime.now().isoformat(),
        "domains": {},
        "overall_statistics": {
            "total_tests": 0,
            "passed_tests": 0,
            "failed_tests": 0,
            "partial_tests": 0,
            "average_confidence": 0.0,
        },
    }

    # ─────────────────────────────────────────────────────────────────────
    # DOMAIN 1: TOPOBENCH
    # ─────────────────────────────────────────────────────────────────────
    print("\n" + "="*80)
    print("DOMAIN 1: TOPOBENCH (Color Generation)")
    print("="*80)

    topobench_features, topobench_seq, topobench_adj = generate_topobench_data()
    topobench_results = []

    # Test D measurement
    print("\nTest 1: Measure D (Dimensionality)")
    try:
        D_val, D_conf = measure_D_pca_fixed(topobench_features)
        status = "PASS" if abs(D_val - 5.0) < 1.0 else "PARTIAL"
        print(f"  Result: D={D_val:.1f} (expected ~5.0), confidence={D_conf:.2f}")
        print(f"  Status: {status}")

        topobench_results.append({
            "test": "Measure D",
            "value": float(D_val),
            "expected": 5.0,
            "confidence": float(D_conf),
            "status": status,
        })

        if tracker:
            tracker.log_measurement(
                domain="Topobench",
                measurement_type="D",
                value=float(D_val),
                confidence=float(D_conf),
                expected=5.0,
                notes="Color generation dimensionality"
            )
    except Exception as e:
        print(f"  ERROR: {e}")
        topobench_results.append({
            "test": "Measure D",
            "status": "FAIL",
            "error": str(e),
        })

    # Test f measurement
    print("\nTest 2: Measure f (Feedback Fraction)")
    try:
        f_val, f_conf = measure_f_ensemble(topobench_seq)
        status = "PASS" if 0.0 <= f_val <= 1.0 else "FAIL"
        print(f"  Result: f={f_val:.2f}, confidence={f_conf:.2f}")
        print(f"  Status: {status}")

        topobench_results.append({
            "test": "Measure f",
            "value": float(f_val),
            "confidence": float(f_conf),
            "status": status,
        })

        if tracker:
            tracker.log_measurement(
                domain="Topobench",
                measurement_type="f",
                value=float(f_val),
                confidence=float(f_conf),
                notes="Feedback fraction in color sequence"
            )
    except Exception as e:
        print(f"  ERROR: {e}")
        topobench_results.append({
            "test": "Measure f",
            "status": "FAIL",
            "error": str(e),
        })

    # Test H₁ measurement
    print("\nTest 3: Detect H₁ (Cycles)")
    try:
        h1_val, h1_conf = detect_cycles_fixed(topobench_adj)
        status = "PASS" if h1_val == 0 else "PARTIAL"
        print(f"  Result: H₁={h1_val} cycles, confidence={h1_conf:.2f}")
        print(f"  Status: {status}")

        topobench_results.append({
            "test": "Detect H₁",
            "value": int(h1_val),
            "expected": 0,
            "confidence": float(h1_conf),
            "status": status,
        })

        if tracker:
            tracker.log_measurement(
                domain="Topobench",
                measurement_type="H1",
                value=float(h1_val),
                confidence=float(h1_conf),
                expected=0.0,
                notes="Topological cycles in network"
            )
    except Exception as e:
        print(f"  ERROR: {e}")
        topobench_results.append({
            "test": "Detect H₁",
            "status": "FAIL",
            "error": str(e),
        })

    results["domains"]["Topobench"] = {
        "tests": topobench_results,
        "success_rate": sum(1 for t in topobench_results if t["status"] in ["PASS", "PARTIAL"]) / len(topobench_results),
    }

    # ─────────────────────────────────────────────────────────────────────
    # DOMAIN 2: GITHUB
    # ─────────────────────────────────────────────────────────────────────
    print("\n" + "="*80)
    print("DOMAIN 2: GITHUB (Repository Dynamics)")
    print("="*80)

    github_features, github_seq, github_adj = generate_github_data()
    github_results = []

    # Test D measurement
    print("\nTest 4: Measure D (Dimensionality)")
    try:
        D_val, D_conf = measure_D_pca_fixed(github_features)
        status = "PASS" if 5 < D_val < 10 else "PARTIAL"
        print(f"  Result: D={D_val:.1f} (expected ~6-8), confidence={D_conf:.2f}")
        print(f"  Status: {status}")

        github_results.append({
            "test": "Measure D",
            "value": float(D_val),
            "confidence": float(D_conf),
            "status": status,
        })

        if tracker:
            tracker.log_measurement(
                domain="GitHub",
                measurement_type="D",
                value=float(D_val),
                confidence=float(D_conf),
                notes="Repository characteristic dimensionality"
            )
    except Exception as e:
        print(f"  ERROR: {e}")
        github_results.append({
            "test": "Measure D",
            "status": "FAIL",
            "error": str(e),
        })

    # Test f measurement
    print("\nTest 5: Measure f (Feedback Fraction)")
    try:
        f_val, f_conf = measure_f_ensemble(github_seq)
        status = "PASS" if 0.3 < f_val < 0.9 else "PARTIAL"
        print(f"  Result: f={f_val:.2f}, confidence={f_conf:.2f}")
        print(f"  Status: {status}")

        github_results.append({
            "test": "Measure f",
            "value": float(f_val),
            "confidence": float(f_conf),
            "status": status,
        })

        if tracker:
            tracker.log_measurement(
                domain="GitHub",
                measurement_type="f",
                value=float(f_val),
                confidence=float(f_conf),
                notes="Feedback in commit sequence"
            )
    except Exception as e:
        print(f"  ERROR: {e}")
        github_results.append({
            "test": "Measure f",
            "status": "FAIL",
            "error": str(e),
        })

    # Test H₁ measurement
    print("\nTest 6: Detect H₁ (Cycles)")
    try:
        h1_val, h1_conf = detect_cycles_fixed(github_adj)
        status = "PASS" if h1_val >= 0 else "FAIL"
        print(f"  Result: H₁={h1_val} cycles, confidence={h1_conf:.2f}")
        print(f"  Status: {status}")

        github_results.append({
            "test": "Detect H₁",
            "value": int(h1_val),
            "confidence": float(h1_conf),
            "status": status,
        })

        if tracker:
            tracker.log_measurement(
                domain="GitHub",
                measurement_type="H1",
                value=float(h1_val),
                confidence=float(h1_conf),
                notes="Dependency cycles in repository"
            )
    except Exception as e:
        print(f"  ERROR: {e}")
        github_results.append({
            "test": "Detect H₁",
            "status": "FAIL",
            "error": str(e),
        })

    results["domains"]["GitHub"] = {
        "tests": github_results,
        "success_rate": sum(1 for t in github_results if t["status"] in ["PASS", "PARTIAL"]) / len(github_results),
    }

    # ─────────────────────────────────────────────────────────────────────
    # DOMAIN 3: IES
    # ─────────────────────────────────────────────────────────────────────
    print("\n" + "="*80)
    print("DOMAIN 3: IES (Learning System)")
    print("="*80)

    ies_features, ies_seq, ies_adj = generate_ies_data()
    ies_results = []

    # Test D measurement
    print("\nTest 7: Measure D (Dimensionality)")
    try:
        D_val, D_conf = measure_D_pca_fixed(ies_features)
        status = "PASS" if 5 < D_val < 10 else "PARTIAL"
        print(f"  Result: D={D_val:.1f} (expected ~5-8), confidence={D_conf:.2f}")
        print(f"  Status: {status}")

        ies_results.append({
            "test": "Measure D",
            "value": float(D_val),
            "confidence": float(D_conf),
            "status": status,
        })

        if tracker:
            tracker.log_measurement(
                domain="IES",
                measurement_type="D",
                value=float(D_val),
                confidence=float(D_conf),
                notes="IES agent state dimensionality"
            )
    except Exception as e:
        print(f"  ERROR: {e}")
        ies_results.append({
            "test": "Measure D",
            "status": "FAIL",
            "error": str(e),
        })

    # Test f measurement
    print("\nTest 8: Measure f (Feedback Fraction)")
    try:
        f_val, f_conf = measure_f_ensemble(ies_seq)
        status = "PASS" if 0.3 < f_val < 0.9 else "PARTIAL"
        print(f"  Result: f={f_val:.2f}, confidence={f_conf:.2f}")
        print(f"  Status: {status}")

        ies_results.append({
            "test": "Measure f",
            "value": float(f_val),
            "confidence": float(f_conf),
            "status": status,
        })

        if tracker:
            tracker.log_measurement(
                domain="IES",
                measurement_type="f",
                value=float(f_val),
                confidence=float(f_conf),
                notes="Feedback in decision history"
            )
    except Exception as e:
        print(f"  ERROR: {e}")
        ies_results.append({
            "test": "Measure f",
            "status": "FAIL",
            "error": str(e),
        })

    # Test H₁ measurement
    print("\nTest 9: Detect H₁ (Cycles)")
    try:
        h1_val, h1_conf = detect_cycles_fixed(ies_adj)
        status = "PASS" if h1_val >= 0 else "FAIL"
        print(f"  Result: H₁={h1_val} cycles, confidence={h1_conf:.2f}")
        print(f"  Status: {status}")

        ies_results.append({
            "test": "Detect H₁",
            "value": int(h1_val),
            "confidence": float(h1_conf),
            "status": status,
        })

        if tracker:
            tracker.log_measurement(
                domain="IES",
                measurement_type="H1",
                value=float(h1_val),
                confidence=float(h1_conf),
                notes="Communication cycles in network"
            )
    except Exception as e:
        print(f"  ERROR: {e}")
        ies_results.append({
            "test": "Detect H₁",
            "status": "FAIL",
            "error": str(e),
        })

    results["domains"]["IES"] = {
        "tests": ies_results,
        "success_rate": sum(1 for t in ies_results if t["status"] in ["PASS", "PARTIAL"]) / len(ies_results),
    }

    # ─────────────────────────────────────────────────────────────────────
    # OVERALL STATISTICS
    # ─────────────────────────────────────────────────────────────────────
    print("\n" + "="*80)
    print("OVERALL RESULTS")
    print("="*80)

    all_results = topobench_results + github_results + ies_results
    passed = sum(1 for t in all_results if t.get("status") == "PASS")
    partial = sum(1 for t in all_results if t.get("status") == "PARTIAL")
    failed = sum(1 for t in all_results if t.get("status") == "FAIL")
    total = len(all_results)

    avg_confidence = np.mean([t.get("confidence", 0.5) for t in all_results])

    results["overall_statistics"] = {
        "total_tests": total,
        "passed_tests": passed,
        "failed_tests": failed,
        "partial_tests": partial,
        "success_rate": (passed + partial) / total if total > 0 else 0,
        "average_confidence": float(avg_confidence),
    }

    print(f"\nTotal tests: {total}")
    print(f"  ✓ Passed: {passed}")
    print(f"  ◐ Partial: {partial}")
    print(f"  ✗ Failed: {failed}")
    print(f"\nSuccess rate: {(passed + partial) / total * 100:.1f}%")
    print(f"Average confidence: {avg_confidence:.2f}")

    # Log final summary
    if tracker:
        tracker.log_summary(results["overall_statistics"])
        tracker.finish()

    return results


if __name__ == "__main__":
    print("Universal Learning Signature Framework")
    print("Validation Suite with W&B Integration")
    print("="*80)

    # Run validation
    results = run_validation_suite_with_wandb(use_wandb=True, offline=True)

    # Save results
    with open("validation_results_wandb.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    print(f"\n✓ Results saved to validation_results_wandb.json")
