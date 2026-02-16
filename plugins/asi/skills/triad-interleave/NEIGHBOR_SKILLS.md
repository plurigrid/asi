# Triad-Interleave Neighbor Skills

**Date**: 2026-01-19
**Trit**: +1 (PLUS - generative)
**Role**: Three-stream scheduling with GF(3) conservation

---

## Core Orchestration Triad

| Skill | Trit | Interface |
|-------|------|-----------|
| **triad-interleave** | +1 | Stream weaving |
| **triadic-skill-orchestrator** | 0 | Skill dispatch |
| **gf3-tripartite** | -1 | Conservation check |

**GF(3)**: (+1) + (0) + (-1) = 0 ✓

---

## Immediate Neighbors

### triadic-skill-orchestrator (0)
**Morphism**: Interleave → Dispatch
```python
schedule = triad_interleave.weave(stream_minus, stream_zero, stream_plus)
orchestrator.dispatch(schedule, seed=0x42D)
```

### gay-mcp (-1)
**Morphism**: Stream → Color sequence
```python
colors = [gay.color_at(i, seed=1069) for i in schedule]
```

### parallel-fanout (+1)
**Morphism**: Interleave → Concurrent execution
```python
fanout.execute([task for task in schedule if independent(task)])
```

### dynamic-sufficiency (-1)
**Morphism**: Schedule → Permission gate
```python
if dynamic_sufficiency.check(schedule):
    execute(schedule)
```

### propagators (0)
**Morphism**: Constraint → Schedule dependencies
```python
deps = propagators.resolve(task_constraints)
schedule = triad_interleave.weave_with_deps(streams, deps)
```

---

## Neighbor Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Color | triad-interleave ⊗ gay-mcp ⊗ splitmixternary | Deterministic coloring |
| Execute | triad-interleave ⊗ parallel-fanout ⊗ dynamic-sufficiency | Safe dispatch |
| Constraint | triad-interleave ⊗ propagators ⊗ gf3-tripartite | Conservation |
