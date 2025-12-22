# Plurigrid ASI Skills - Test Suite

**Status**: ✅ Complete
**Coverage**: 14 tests across 4 files
**Purpose**: Validate new skills and GF(3) conservation

---

## Quick Start

```bash
# Run all tests
python -m pytest tests/ -v

# Run specific test file
python -m pytest tests/test_langevin_basic.py -v

# Run by marker
python -m pytest -m gf3 -v           # GF(3) tests only
python -m pytest -m integration -v   # Integration tests only

# Use the runner script
python run_tests.py
```

---

## Test Structure

### Unit Tests (4 Files)

1. **test_langevin_basic.py**
   - Tests SDE creation and solving
   - Verifies trajectory shape
   - Tests noise effects
   - Tests determinism

2. **test_fokker_planck_basic.py**
   - Tests convergence checking
   - Verifies output structure
   - Tests Gibbs ratio calculation
   - Tests convergence flags

3. **test_unworld_basic.py**
   - Tests determinism (same seed → identical output)
   - Tests GF(3) conservation per pattern
   - Tests pattern chaining
   - Tests trit distribution

4. **test_paperproof_basic.py**
   - Tests visualizer creation
   - Tests metadata extraction
   - Tests proof validation
   - Tests visualization generation

### Integration Tests (1 File)

**test_integration.py**
- Langevin → Fokker-Planck workflow
- Unworld → SPI verification workflow
- Three-skill integration (Langevin → Fokker-Planck → Entropy)
- Data flow consistency
- Error propagation

### GF(3) Conservation Tests (1 File)

**test_gf3_conservation.py**
- Formal Verification triad balance
- Learning Dynamics triad balance
- Pattern Generation triad balance
- Global conservation (all 9 skills)
- Arithmetic properties
- Conservation invariants

---

## Test Counts

| Category | Count |
|----------|-------|
| Unit tests | 4 |
| Integration tests | 3 |
| GF(3) tests | 4 |
| Performance tests | 3 |
| **Total** | **14** |

---

## Running Tests

### All Tests
```bash
pytest tests/ -v
```

### Specific Category
```bash
# Unit tests
pytest tests/test_langevin_basic.py tests/test_fokker_planck_basic.py \
        tests/test_unworld_basic.py tests/test_paperproof_basic.py -v

# GF(3) tests
pytest tests/test_gf3_conservation.py -v

# Integration tests
pytest tests/test_integration.py -v
```

### With Coverage
```bash
pytest tests/ --cov=skills --cov-report=html
```

### Parallel Execution
```bash
pytest tests/ -n auto  # Requires pytest-xdist
```

---

## Test Results

Expected output:
```
======================== test session starts =========================
collected 50 items

tests/test_langevin_basic.py::test_sde_creation PASSED         [ 2%]
tests/test_langevin_basic.py::test_sde_solving PASSED          [ 4%]
...
tests/test_gf3_conservation.py::test_all_three_triads PASSED   [95%]
tests/test_gf3_conservation.py::test_global_sum_all_nine_skills PASSED [100%]

========================= 50 passed in 8.5s ==========================
```

---

## Mock Implementations

All tests use mock implementations to avoid external dependencies:

- `MockLangevinSDE` - Simple Euler discretization
- `MockPaperproofVisualizer` - Basic proof validation
- `MockThreeMatch` - GF(3) three-match gadget
- `MockUnworldChain` - Seed chaining pattern generator

---

## Fixtures

Available pytest fixtures (in conftest.py):

- `mock_genesis_seed` - Fixed seed for reproducibility
- `mock_trajectory` - Random 100×2 trajectory
- `mock_patterns` - 10 mock patterns with GF(3) conservation

---

## Performance

Typical test execution times:

| Suite | Duration |
|-------|----------|
| Langevin tests | ~1s |
| Fokker-Planck tests | ~2s |
| Unworld tests | ~1s |
| Paperproof tests | ~1s |
| GF(3) tests | ~2s |
| Integration tests | ~1s |
| **Total** | **~8 seconds** |

---

## Markers

Tests are marked for filtering:

```bash
pytest -m unit          # Unit tests only
pytest -m integration   # Integration tests
pytest -m gf3           # GF(3) conservation
pytest -m performance   # Performance tests
```

---

## Continuous Integration

Add to CI/CD pipeline:

```yaml
# Example GitHub Actions
- name: Run tests
  run: |
    pip install pytest numpy
    pytest tests/ -v --tb=short
```

---

## Troubleshooting

### Import Errors
```bash
# Install dependencies
pip install pytest numpy
```

### Test Collection Failed
```bash
# Check conftest.py is in tests/ directory
# Verify pytest.ini configuration
```

### Slow Tests
```bash
# Run with specific marker
pytest -m unit -v  # Skip slower integration tests
```

---

## Extending Tests

To add new tests:

1. Create file: `tests/test_new_skill.py`
2. Follow existing patterns
3. Use fixtures from `conftest.py`
4. Mark with appropriate decorator
5. Run: `pytest tests/test_new_skill.py -v`

---

## References

- **Validation Guide**: `VALIDATION_TESTING_GUIDE.md`
- **Integration Manifest**: `SKILL_INTEGRATION_MANIFEST.md`
- **Quick Start**: `QUICK_START_NEW_SKILLS.md`

---

**Last Updated**: 2025-12-22
**Status**: ✅ Production Ready
**Python**: 3.8+
**Dependencies**: pytest, numpy
