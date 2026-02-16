# TIDAR: Correct by Construction

> Triadic Interleaving Dispatch with Agents for Reading/writing — where invalid states are unrepresentable

## Core Insight

**Correct by construction** means: if it compiles/type-checks, GF(3) is conserved.

```
TIDAR Tree (depth 3):
                        Root (0)
           ┌──────────────┼──────────────┐
        -1 │              0              │ +1
       ┌───┼───┐      ┌───┼───┐      ┌───┼───┐
      -1   0  +1    -1   0  +1    -1   0  +1
     ┌┴┐ ┌┴┐ ┌┴┐   ┌┴┐ ┌┴┐ ┌┴┐   ┌┴┐ ┌┴┐ ┌┴┐
     27 leaves (3³), each balanced triad sums to 0
```

## Type-Level Invariants

```python
# GF(3) is enforced at construction — no runtime checks needed
triad = Triad.build(minus, middle, plus)  # Only way to create
# Compile-time: triad.sum() == 0 is GUARANTEED
```

## The 40-Agent Structure

| Level | Agents | Role |
|-------|--------|------|
| 0 | 1 | Root coordinator (ERGODIC) |
| 1 | 3 | Branch managers (-1, 0, +1) |
| 2 | 9 | Sub-coordinators (3×3) |
| 3 | 27 | Leaf workers (3³) |
| **Total** | **40** | **GF(3) conserved at each level** |

## Correct-by-Construction Rules

1. **Triads are atomic**: Cannot create partial triads
2. **Balance is intrinsic**: Triad = (MINUS, MIDDLE, PLUS), sum = 0
3. **Tree is complete**: Every node has exactly 0 or 3 children
4. **Pre-hooks are mandatory**: Read before write, encoded in types
5. **Middle-path collapse**: Only MIDDLE nodes emit final results

## Usage

```python
from tidar_cbc import TIDARTree, Triad, Trit

# Build tree — only balanced constructions allowed
tree = TIDARTree.build_depth_3(seed=1069)

# Cannot create unbalanced:
# Triad(Trit.PLUS, Trit.PLUS, Trit.PLUS)  # TYPE ERROR

# Dispatch with pre-hooks
async for result in tree.dispatch_with_prehooks(task):
    # Results only from MIDDLE path (proven by types)
    assert result.source.trit == Trit.MIDDLE
```

## Files

- `tidar_cbc.py` — Core correct-by-construction implementation
- `tidar_cbc_test.py` — Property-based tests (Hypothesis)

## Key Properties

| Property | How Enforced |
|----------|--------------|
| GF(3) conservation | Constructor only accepts balanced triads |
| 40-agent count | Tree depth fixed at 3, branching factor 3 |
| Pre-hook ordering | Read/Write phases in state machine types |
| Middle-path collapse | Only `MiddleAgent` has `emit()` method |

## trit: 0 (ERGODIC)

TIDAR is a coordinator skill — it balances, never sources or sinks.
