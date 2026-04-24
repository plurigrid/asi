---
name: world-replay-buffer
description: Maximally snapshotted replay buffer with DuckLake embedding VSS and moments of interaction for world-transition storage
trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
worlds: true
---

# World Replay Buffer

**Trit**: 0 (ZERO)
**Domain**: Reinforcement Learning / World Transitions
**Principle**: Worlds (a-z) as successor worlds with GF(3) balanced sampling

## Overview

A maximally snapshotted replay buffer system for storing and retrieving world-transitions with:
- **DuckDB persistence** with vector similarity search (VSS)
- **GF(3) Galois Field classification** {-1=MINUS, 0=ZERO, +1=PLUS}
- **Trit-tick timing** at 1/141,120,000 second (~7.09 ns) precision
- **Content-addressed deduplication** via SHA-256 hashing
- **Play/Coplay Arena semantics** for action-observation pairs

## Mathematical Definition

```
REPLAY: WorldState × Action → WorldState' × Observation × Reward
GF3_COLOR: Experience → {-1, 0, +1}
TRIT_TICK: 1 / 141_120_000 seconds ≈ 7.09 nanoseconds
```

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                   World Replay Buffer                    │
├─────────────────────────────────────────────────────────┤
│  replay_buffer.lpy    │ Pure Basilisp in-memory buffer  │
│  replay_buffer.py     │ Python + DuckDB/VSS persistence │
│  replay_orchestrator.py│ Unified orchestrator with DB   │
│  replay_bridge.lpy    │ Basilisp-Python interop bridge  │
└─────────────────────────────────────────────────────────┘
```

## Key Components

### 1. Experience Storage

```clojure
;; Basilisp experience structure
{:world-from "world-a"
 :world-to   "world-b"
 :action     {:play [:move :forward]}
 :obs        {:coplay [:sensor :reading]}
 :reward     1.0
 :timestamp  1711471200.0
 :gf3-color  1}  ; PLUS
```

### 2. GF(3) Classification

Uses SplitMix64 deterministic hashing for reproducible coloring:

```python
def gf3_color(content: str) -> int:
    """GF(3) classification via SplitMix64 hash."""
    h = splitmix64_hash(content)
    return (h % 3) - 1  # {-1, 0, +1}
```

### 3. World Transitions

Worlds are labeled a-z as **successor worlds**, NOT todos:

```
world-a → world-b → world-c → ... → world-z
```

Each transition stores:
- Source world state
- Action taken (play)
- Resulting observation (coplay)
- Reward signal
- GF(3) color for balanced sampling

### 4. Prioritized Sampling

Balanced sampling across GF(3) classes ensures no class dominates:

```clojure
(defn sample-balanced-gf3
  "Sample experiences balanced across GF(3) classes."
  [buffer n]
  (let [by-color (group-by :gf3-color buffer)
        per-class (max 1 (quot n 3))]
    (->> (vals by-color)
         (mapcat #(take per-class (shuffle %)))
         (take n))))
```

## DuckDB Schema

```sql
CREATE SEQUENCE IF NOT EXISTS exp_id_seq;
CREATE TABLE IF NOT EXISTS experiences (
    id INTEGER PRIMARY KEY DEFAULT nextval('exp_id_seq'),
    world_from TEXT NOT NULL,
    world_to TEXT NOT NULL,
    action_json TEXT NOT NULL,
    obs_json TEXT NOT NULL,
    reward DOUBLE NOT NULL,
    timestamp_ns BIGINT NOT NULL,
    gf3_color INTEGER NOT NULL,
    content_hash TEXT UNIQUE NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_gf3 ON experiences(gf3_color);
CREATE INDEX IF NOT EXISTS idx_world_from ON experiences(world_from);
```

## Usage

### Basilisp (Pure In-Memory)

```clojure
(ns replay-buffer)

;; Add experience
(def exp {:world-from "world-a"
          :world-to "world-b"
          :action {:type :move}
          :obs {:type :sensor}
          :reward 1.0})
(add-experience! buffer exp)

;; Sample balanced
(sample-balanced-gf3 @buffer 10)
```

### Python (With Persistence)

```python
from replay_orchestrator import ReplayOrchestrator

orch = ReplayOrchestrator()
orch.store_experience(
    world_from="world-a",
    world_to="world-b",
    action={"type": "move"},
    observation={"type": "sensor"},
    reward=1.0
)
samples = orch.sample_balanced(n=10)
```

### Basilisp-Python Bridge

```clojure
(ns replay-bridge
  (:import importlib))

(def orch (get-orchestrator))
(store-experience! orch {:world-from "world-a" ...})
```

## Integration with GF(3)

This skill participates in triadic composition:
- **Trit 0** (ZERO): Neutral/balanced storage
- **Conservation**: Σ trits ≡ 0 (mod 3) across skill triplets
- **Balanced Sampling**: Equal representation of {-1, 0, +1} classes

## Trit-Tick Timing

```python
TRIT_TICK = 1 / 141_120_000  # ~7.09 nanoseconds
timestamp_tritticks = int(time.time() / TRIT_TICK)
```

## Files

Located in `/Users/alice/worlds/`:
- `replay_buffer.lpy` - Pure Basilisp implementation
- `replay_buffer.py` - Python with DuckDB
- `replay_orchestrator.py` - Unified orchestrator
- `replay_bridge.lpy` - Basilisp-Python bridge

## Related Skills

- world-hopping (trit +1) - Navigate between worlds
- worlding (trit -1) - World construction
- trajectory (trit -1) - Path through phase space
- gf3-classification (trit 0) - Triadic classification
- ducklake (trit +1) - DuckDB lakehouse

---

**Skill Name**: world-replay-buffer
**Type**: Reinforcement Learning / Experience Storage
**Trit**: 0 (ZERO)
**GF(3)**: Conserved in triplet composition

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Mobius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No world revisited in transition chain
2. **Mobius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Content Dedup**: SHA-256 ensures no duplicate experiences

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
World Transition:
  world_a →[action]→ world_b →[action]→ world_c
  
GF(3) Balance:
  |{exp : color = -1}| ≈ |{exp : color = 0}| ≈ |{exp : color = +1}|
```
