---
name: triangle-metrics
description: Triangle Metrics Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Triangle Metrics Skill

**Trit**: 0 (ERGODIC - synthesizer/coordinator)
**Purpose**: Unify all triangle inequality skills into a coherent metric space

---

## Cross-Referenced Skills

| Skill | Guarantee | Integration Point |
|-------|-----------|-------------------|
| **glass-hopping** | ≪ order transitivity | `TriangleInequality` Narya type |
| **world-hopping** | Dijkstra pruning | `d13 <= d12 + d23` constraint |
| **glass-bead-game** | Propagator constraint | `world_distance` comparisons |
| **epistemic-arbitrage** | Knowledge transfer bound | `d(A,C) ≤ d(A,B) + d(B,C)` |
| **l-space** | Navigation metric | `:triangle_inequality` traversal |
| **open-games** | Play/coplay equilibrium | `equilibrium ⟺ d(a,c) ≤ d(a,b) + d(b,c)` |

---

## Unified Interface

```julia
# Abstract metric interface all skills implement
abstract type TriangleMetric end

struct WorldDistance <: TriangleMetric
    d12::Float64
    d23::Float64
    d13::Float64
end

function triangle_valid(m::WorldDistance)::Bool
    m.d13 ≤ m.d12 + m.d23
end

# Skill-specific implementations
struct GlassHoppingMetric <: TriangleMetric
    h12::Bridge  # W₁ ≪ W₂
    h23::Bridge  # W₂ ≪ W₃
    # Transitivity guarantees h13
end

struct OpenGamesMetric <: TriangleMetric
    play::Strategy    # Forward distance
    coplay::Strategy  # Backward distance
    # Equilibrium ⟺ triangle satisfied
end
```

---

## Mutual Awareness Protocol

When any triangle skill is invoked:

1. **Check**: Query other loaded triangle skills
2. **Validate**: Ensure distances are consistent across all
3. **Propagate**: Share metric updates to siblings
4. **Witness**: Generate Narya proof if all agree

```narya
-- Unified triangle witness
def UnifiedTriangle 
    (glass : GlassHopping.Bridge)
    (world : WorldHopping.Path)
    (game  : OpenGames.Equilibrium)
    : TriangleValidated
```

---

## DuckLake Integration

```sql
-- Query triangle-validated interactions
SELECT a.id, a.trit, a.triangle_valid,
       b.id as next_id, b.trit