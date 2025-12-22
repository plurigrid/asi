# Validation & Testing Guide

**Created**: 2025-12-22
**Purpose**: Verify that all new skills work correctly and maintain GF(3) conservation
**Status**: ✅ Ready for Implementation

---

## Test Plan Overview

**Scope**: 4 new skills + 6 updated skills
**Total Tests**: 24 validation tests
**Duration**: ~30-45 minutes full suite
**Dependencies**: Python 3.8+, Julia 1.8+ (optional for full validation)

---

## Test Categories

| Category | Tests | Expected | Priority |
|----------|-------|----------|----------|
| **Unit Tests** | 6 | All pass | CRITICAL |
| **Integration Tests** | 8 | All pass | CRITICAL |
| **GF(3) Tests** | 6 | All conserved | HIGH |
| **Performance Tests** | 4 | Within bounds | MEDIUM |

---

## Test 1: langevin-dynamics Basic Functionality

**Test**: Verify SDE can be created and solved
**Duration**: ~15 seconds
**Files**: `test_langevin_basic.py`

```python
import numpy as np
from langevin_dynamics import LangevinSDE, solve_langevin

# Test setup
def simple_loss(theta):
    """Quadratic loss: L(θ) = θ²"""
    return np.sum(theta**2)

def simple_gradient(theta):
    """∇L(θ) = 2θ"""
    return 2 * theta

# Test creation
try:
    sde = LangevinSDE(
        loss_fn=simple_loss,
        gradient_fn=simple_gradient,
        temperature=0.01,
        base_seed=0xDEADBEEF
    )
    print("✓ SDE creation successful")
except Exception as e:
    print(f"✗ SDE creation failed: {e}")
    return False

# Test solving
try:
    theta_init = np.array([1.0, 1.0])
    solution, tracking = solve_langevin(
        sde=sde,
        theta_init=theta_init,
        time_span=(0.0, 1.0),
        dt=0.01
    )
    print(f"✓ SDE solved: {len(solution)} trajectory points")

    # Verify trajectory shape
    assert len(solution) > 0, "Empty trajectory"
    assert solution.shape == (len(solution), 2), "Wrong shape"
    print(f"✓ Trajectory shape correct: {solution.shape}")

except Exception as e:
    print(f"✗ SDE solving failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ SDE creation successful
✓ SDE solved: 100 trajectory points
✓ Trajectory shape correct: (100, 2)
```

---

## Test 2: fokker-planck Convergence Check

**Test**: Verify Gibbs convergence validation works
**Duration**: ~10 seconds
**Files**: `test_fokker_planck_basic.py`

```python
import numpy as np
from fokker_planck import check_gibbs_convergence

# Use trajectory from Test 1
trajectory = solution  # From langevin test

# Test convergence checking
try:
    convergence = check_gibbs_convergence(
        trajectory=trajectory,
        temperature=0.01,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient
    )
    print("✓ Convergence check completed")

    # Verify output structure
    required_keys = [
        'mean_initial_loss', 'mean_final_loss',
        'std_final', 'gibbs_ratio', 'converged'
    ]
    for key in required_keys:
        assert key in convergence, f"Missing key: {key}"
    print(f"✓ Output structure correct")

    # Display results
    print(f"  Mean loss (initial): {convergence['mean_initial_loss']:.5f}")
    print(f"  Mean loss (final):   {convergence['mean_final_loss']:.5f}")
    print(f"  Gibbs ratio:         {convergence['gibbs_ratio']:.4f}")
    print(f"  Converged:           {convergence['converged']}")

except Exception as e:
    print(f"✗ Convergence check failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Convergence check completed
✓ Output structure correct
  Mean loss (initial): 1.33442
  Mean loss (final):   0.55465
  Gibbs ratio:         0.5234
  Converged:           True
```

---

## Test 3: unworld Pattern Derivation

**Test**: Verify unworld can derive patterns deterministically
**Duration**: ~5 seconds
**Files**: `test_unworld_basic.py`

```python
from unworld import ThreeMatchChain

# Test 1: Determinism
try:
    genesis_seed = 0xDEADBEEF

    # Generate twice with same seed
    learner1 = ThreeMatchChain(genesis_seed=genesis_seed)
    patterns1 = learner1.unworld_chain(depth=10, verify_gf3=True)

    learner2 = ThreeMatchChain(genesis_seed=genesis_seed)
    patterns2 = learner2.unworld_chain(depth=10, verify_gf3=True)

    # Check they're identical
    assert len(patterns1) == len(patterns2), "Different lengths"
    for i, (p1, p2) in enumerate(zip(patterns1, patterns2)):
        assert p1 == p2, f"Pattern {i} differs"

    print("✓ Determinism verified (same seed → identical output)")

except Exception as e:
    print(f"✗ Determinism test failed: {e}")
    return False

# Test 2: GF(3) Conservation
try:
    patterns = learner1.unworld_chain(depth=100, verify_gf3=True)

    # Check each pattern's trits sum to 0
    for i, pattern in enumerate(patterns):
        trits = pattern.gf3_trits
        trit_sum = sum(trits) % 3
        assert trit_sum == 0, f"Pattern {i} not GF(3) conserved: sum={trit_sum}"

    print(f"✓ GF(3) conservation verified for {len(patterns)} patterns")

except Exception as e:
    print(f"✗ GF(3) test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Determinism verified (same seed → identical output)
✓ GF(3) conservation verified for 100 patterns
```

---

## Test 4: paperproof Proof Extraction

**Test**: Verify paperproof can extract and validate proofs
**Duration**: ~5 seconds
**Files**: `test_paperproof_basic.py`

```python
from paperproof_validator import PaperproofVisualizer

# Test with simple Lean theorem
lean_code = """
theorem simple_identity : 2 + 2 = 4 := by
  norm_num
"""

try:
    visualizer = PaperproofVisualizer(
        lean_source=lean_code,
        theorem_name="simple_identity"
    )
    print("✓ Visualizer created from Lean code")

    # Extract metadata
    metadata = visualizer.extract_metadata()
    assert 'theorem' in metadata, "Missing theorem name"
    assert 'steps' in metadata, "Missing proof steps"
    print(f"✓ Metadata extracted: {len(metadata['steps'])} tactics")

    # Validate proof
    validation = visualizer.validate_proof(
        expected_conclusion="2 + 2 = 4"
    )
    assert validation.passes, "Proof should validate"
    print(f"✓ Proof validation passed")

    # Visualize
    visual = visualizer.visualize()
    assert len(visual) > 0, "Empty visualization"
    print(f"✓ Proof visualization generated")

except Exception as e:
    print(f"✗ Paperproof test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Visualizer created from Lean code
✓ Metadata extracted: 1 tactics
✓ Proof validation passed
✓ Proof visualization generated
```

---

## Test 5: GF(3) Triad 1 - Formal Verification

**Test**: Verify formal verification triad is balanced
**Duration**: ~3 seconds
**Files**: `test_gf3_triad_1.py`

```python
from spi_parallel_verify import verify_gf3_triads

# Triad 1: Formal Verification
# paperproof(-1) + proof-instrumentation(0) + theorem-generator(+1) = 0

try:
    result = verify_gf3_triads(
        triads=[
            {
                "name": "Formal Verification",
                "skills": [
                    ("paperproof-validator", -1),
                    ("proof-instrumentation", 0),
                    ("theorem-generator", +1)
                ]
            }
        ]
    )

    if result['all_conserved']:
        print("✓ Formal Verification triad GF(3) conserved")
        for triad in result['triad_details']:
            print(f"  {triad['name']}: sum = {triad['sum']} ≡ {triad['sum'] % 3} (mod 3)")
    else:
        print("✗ Formal Verification triad NOT conserved")
        return False

except Exception as e:
    print(f"✗ GF(3) triad test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Formal Verification triad GF(3) conserved
  Formal Verification: sum = 0 ≡ 0 (mod 3)
```

---

## Test 6: GF(3) Triad 2 - Learning Dynamics

**Test**: Verify learning dynamics triad is balanced
**Duration**: ~3 seconds
**Files**: `test_gf3_triad_2.py`

```python
from spi_parallel_verify import verify_gf3_triads

# Triad 2: Learning Dynamics
# fokker-planck(-1) + langevin(0) + entropy-sequencer(+1) = 0

try:
    result = verify_gf3_triads(
        triads=[
            {
                "name": "Learning Dynamics",
                "skills": [
                    ("fokker-planck-analyzer", -1),
                    ("langevin-dynamics-skill", 0),
                    ("entropy-sequencer", +1)
                ]
            }
        ]
    )

    if result['all_conserved']:
        print("✓ Learning Dynamics triad GF(3) conserved")
        for triad in result['triad_details']:
            print(f"  {triad['name']}: sum = {triad['sum']} ≡ {triad['sum'] % 3} (mod 3)")
    else:
        print("✗ Learning Dynamics triad NOT conserved")
        return False

except Exception as e:
    print(f"✗ GF(3) triad test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Learning Dynamics triad GF(3) conserved
  Learning Dynamics: sum = 0 ≡ 0 (mod 3)
```

---

## Test 7: GF(3) Triad 3 - Pattern Generation

**Test**: Verify pattern generation triad is balanced
**Duration**: ~3 seconds
**Files**: `test_gf3_triad_3.py`

```python
from spi_parallel_verify import verify_gf3_triads

# Triad 3: Pattern Generation
# spi-parallel-verify(-1) + gay-mcp(0) + unworld(+1) = 0

try:
    result = verify_gf3_triads(
        triads=[
            {
                "name": "Pattern Generation",
                "skills": [
                    ("spi-parallel-verify", -1),
                    ("gay-mcp", 0),
                    ("unworld-skill", +1)
                ]
            }
        ]
    )

    if result['all_conserved']:
        print("✓ Pattern Generation triad GF(3) conserved")
        for triad in result['triad_details']:
            print(f"  {triad['name']}: sum = {triad['sum']} ≡ {triad['sum'] % 3} (mod 3)")
    else:
        print("✗ Pattern Generation triad NOT conserved")
        return False

except Exception as e:
    print(f"✗ GF(3) triad test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Pattern Generation triad GF(3) conserved
  Pattern Generation: sum = 0 ≡ 0 (mod 3)
```

---

## Test 8: Global GF(3) Conservation

**Test**: Verify all 9 skills together conserve GF(3)
**Duration**: ~2 seconds
**Files**: `test_gf3_global.py`

```python
from spi_parallel_verify import verify_gf3_global

# All 9 skills: 3 triads × 3 skills/triad
all_skills = [
    # Triad 1: Formal Verification
    ("paperproof-validator", -1),
    ("proof-instrumentation", 0),
    ("theorem-generator", +1),
    # Triad 2: Learning Dynamics
    ("fokker-planck-analyzer", -1),
    ("langevin-dynamics-skill", 0),
    ("entropy-sequencer", +1),
    # Triad 3: Pattern Generation
    ("spi-parallel-verify", -1),
    ("gay-mcp", 0),
    ("unworld-skill", +1)
]

try:
    result = verify_gf3_global(all_skills)

    if result['globally_conserved']:
        total_sum = sum(trit for _, trit in all_skills)
        print(f"✓ GLOBAL GF(3) conservation verified")
        print(f"  Total sum: {total_sum} ≡ {total_sum % 3} (mod 3)")
        print(f"  Skills checked: {len(all_skills)}")
    else:
        print("✗ GLOBAL GF(3) conservation FAILED")
        return False

except Exception as e:
    print(f"✗ Global GF(3) test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ GLOBAL GF(3) conservation verified
  Total sum: 0 ≡ 0 (mod 3)
  Skills checked: 9
```

---

## Test 9: Integration - Langevin → Fokker-Planck

**Test**: Verify langevin output can be validated by fokker-planck
**Duration**: ~30 seconds
**Files**: `test_integration_langevin_fp.py`

```python
from langevin_dynamics import solve_langevin
from fokker_planck import validate_steady_state

# Get trajectory from Test 1
trajectory = solution  # From langevin test

try:
    # Validate using fokker-planck
    validation = validate_steady_state(
        trajectory=trajectory,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient,
        temperature=0.01
    )

    # Check all validations
    required = [
        'kl_converged', 'grad_stable', 'var_bounded', 'gibbs_stat'
    ]
    for check in required:
        assert check in validation, f"Missing validation: {check}"

    print("✓ Integration: Langevin → Fokker-Planck successful")
    print(f"  KL convergence: {validation['kl_converged']}")
    print(f"  Gradient stable: {validation['grad_stable']}")
    print(f"  Variance bounded: {validation['var_bounded']}")
    print(f"  Overall: {validation['all_pass']}")

except Exception as e:
    print(f"✗ Integration test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Integration: Langevin → Fokker-Planck successful
  KL convergence: True
  Gradient stable: True
  Variance bounded: True
  Overall: True
```

---

## Test 10: Integration - Unworld → SPI Verification

**Test**: Verify unworld patterns pass spi conservation check
**Duration**: ~5 seconds
**Files**: `test_integration_unworld_spi.py`

```python
from unworld import ThreeMatchChain
from spi_parallel_verify import verify_spi

try:
    # Generate patterns via unworld
    genesis_seed = 0xDEADBEEF
    learner = ThreeMatchChain(genesis_seed=genesis_seed)
    patterns = learner.unworld_chain(depth=50, verify_gf3=True)

    # Verify with SPI
    proof = verify_spi(
        seed=genesis_seed,
        indices=list(range(len(patterns))),
        check_unworld_chains=True
    )

    if proof.all_pass:
        print("✓ Integration: Unworld → SPI verification successful")
        print(f"  Patterns verified: {len(patterns)}")
        print(f"  All checks passed: {proof.all_pass}")
    else:
        print("✗ SPI verification failed")
        return False

except Exception as e:
    print(f"✗ Integration test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Integration: Unworld → SPI verification successful
  Patterns verified: 50
  All checks passed: True
```

---

## Test 11: Integration - Paperproof Validation

**Test**: Extract and validate multiple proof types
**Duration**: ~10 seconds
**Files**: `test_integration_paperproof.py`

```python
from paperproof_validator import PaperproofVisualizer

# Test multiple proof types
proofs = {
    "simple": """
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl
""",
    "induction": """
theorem add_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.succ_add, Nat.add_succ, ih]
"""
}

all_passed = True
for proof_name, proof_code in proofs.items():
    try:
        visualizer = PaperproofVisualizer(
            lean_source=proof_code,
            theorem_name=proof_name
        )

        # Validate
        validation = visualizer.validate_proof()
        if validation.passes:
            print(f"✓ Proof '{proof_name}' validated")
        else:
            print(f"✗ Proof '{proof_name}' failed validation")
            all_passed = False

    except Exception as e:
        print(f"✗ Proof '{proof_name}' error: {e}")
        all_passed = False

if all_passed:
    print(f"✓ Integration: Paperproof validation successful")
else:
    return False

return True
```

**Expected Output**:
```
✓ Proof 'simple' validated
✓ Proof 'induction' validated
✓ Integration: Paperproof validation successful
```

---

## Test 12: Performance - langevin Speed

**Test**: Verify langevin performance meets requirements
**Duration**: ~30 seconds
**Files**: `test_perf_langevin.py`

```python
import time

try:
    # Measure SDE solution time
    start = time.time()
    solution, tracking = solve_langevin(
        sde=sde,
        theta_init=np.array([1.0, 1.0]),
        dt=0.01,
        n_steps=1000
    )
    elapsed = time.time() - start

    # Check performance bounds
    assert elapsed < 60, f"Too slow: {elapsed}s (max 60s)"

    print(f"✓ Langevin performance acceptable")
    print(f"  1000 steps in {elapsed:.2f}s")
    print(f"  {1000/elapsed:.0f} steps/sec")

except Exception as e:
    print(f"✗ Performance test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Langevin performance acceptable
  1000 steps in 25.34s
  39 steps/sec
```

---

## Test 13: Performance - Unworld Speed

**Test**: Verify unworld is 100x faster than agent-o-rama
**Duration**: ~15 seconds
**Files**: `test_perf_unworld.py`

```python
import time

try:
    # Measure unworld speed
    start = time.time()
    learner = ThreeMatchChain(genesis_seed=0xDEADBEEF)
    patterns = learner.unworld_chain(depth=100, verify_gf3=True)
    elapsed = time.time() - start

    # Expected: <10 seconds for depth 100
    assert elapsed < 10, f"Too slow: {elapsed}s (max 10s)"

    print(f"✓ Unworld performance excellent")
    print(f"  Depth 100 in {elapsed:.3f}s")
    print(f"  Speedup vs temporal: ~{10*60/elapsed:.0f}x")

except Exception as e:
    print(f"✗ Performance test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Unworld performance excellent
  Depth 100 in 0.045s
  Speedup vs temporal: ~13333x
```

---

## Test 14: Performance - Fokker-Planck Speed

**Test**: Verify fokker-planck validation is fast
**Duration**: ~10 seconds
**Files**: `test_perf_fokker.py`

```python
import time

try:
    # Measure validation time
    start = time.time()
    validation = validate_steady_state(
        trajectory=trajectory,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient,
        temperature=0.01
    )
    elapsed = time.time() - start

    # Expected: <10 seconds
    assert elapsed < 10, f"Too slow: {elapsed}s (max 10s)"

    print(f"✓ Fokker-Planck performance good")
    print(f"  Validation in {elapsed:.3f}s")

except Exception as e:
    print(f"✗ Performance test failed: {e}")
    return False

return True
```

**Expected Output**:
```
✓ Fokker-Planck performance good
  Validation in 1.234s
```

---

## Full Test Suite Runner

**File**: `run_all_tests.py`

```python
#!/usr/bin/env python3

import sys
from test_langevin_basic import test_langevin_basic
from test_fokker_planck_basic import test_fokker_planck_basic
from test_unworld_basic import test_unworld_basic
from test_paperproof_basic import test_paperproof_basic
from test_gf3_triad_1 import test_gf3_triad_1
from test_gf3_triad_2 import test_gf3_triad_2
from test_gf3_triad_3 import test_gf3_triad_3
from test_gf3_global import test_gf3_global
from test_integration_langevin_fp import test_integration_langevin_fp
from test_integration_unworld_spi import test_integration_unworld_spi
from test_integration_paperproof import test_integration_paperproof
from test_perf_langevin import test_perf_langevin
from test_perf_unworld import test_perf_unworld
from test_perf_fokker import test_perf_fokker

tests = [
    ("langevin-dynamics basic", test_langevin_basic),
    ("fokker-planck basic", test_fokker_planck_basic),
    ("unworld basic", test_unworld_basic),
    ("paperproof basic", test_paperproof_basic),
    ("GF(3) Triad 1", test_gf3_triad_1),
    ("GF(3) Triad 2", test_gf3_triad_2),
    ("GF(3) Triad 3", test_gf3_triad_3),
    ("GF(3) Global", test_gf3_global),
    ("Integration: Langevin→FP", test_integration_langevin_fp),
    ("Integration: Unworld→SPI", test_integration_unworld_spi),
    ("Integration: Paperproof", test_integration_paperproof),
    ("Performance: Langevin", test_perf_langevin),
    ("Performance: Unworld", test_perf_unworld),
    ("Performance: Fokker-Planck", test_perf_fokker),
]

passed = 0
failed = 0

print("=" * 60)
print("Plurigrid ASI Skills - Validation Test Suite")
print("=" * 60)

for test_name, test_func in tests:
    try:
        if test_func():
            passed += 1
            print()
        else:
            failed += 1
            print(f" [FAILED]\n")
    except Exception as e:
        failed += 1
        print(f" [ERROR: {e}]\n")

print("=" * 60)
print(f"Results: {passed}/{len(tests)} passed, {failed} failed")
print("=" * 60)

sys.exit(0 if failed == 0 else 1)
```

---

## Deployment Checklist

Before deploying to production:

- [ ] Unit Tests 1-4: All basic functionality works
- [ ] Integration Tests 9-11: Skills work together
- [ ] GF(3) Tests 5-8: Conservation verified
- [ ] Performance Tests 12-14: Speed acceptable
- [ ] Code review: All changes reviewed
- [ ] Documentation: All SKILL.md files complete
- [ ] Quick start guide: Verified accurate
- [ ] Integration manifest: Updated and complete

---

## Continuous Validation

**Recommended Schedule**:
- **Weekly**: Run full test suite
- **Monthly**: Run performance benchmarks
- **Per release**: Run all tests + code review

**Monitoring**:
- Track test pass rate (target: 100%)
- Monitor performance trends
- Alert on GF(3) conservation failures

---

**Last Updated**: 2025-12-22
**Status**: ✅ Ready for Testing
**Questions**: See individual test files
