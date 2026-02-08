---
name: plr-thread-coloring
description: PLR (Parallel/Leading-tone/Relative) transitions for thread coloring. One-hot keyspace reduction to GF(3) trits for behavior indexing. Grows perception/action information field capacity through efficient user illusion.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# PLR Thread Coloring

> *The first color IS the thread. One-hot → trit → behavior.*

## Core Thesis

Thread identifiers (T-xxxxxxxx) are **seeds**. The first color derived from the seed IS the thread's identity. PLR transformations navigate the color space while preserving common tones (2/3 components stable).

```
Thread ID → Hash → Seed → SplitMix64 → First Color → Identity
                              ↓
                    PLR Transitions → Color Path → Behavior Trace
                              ↓
                    One-Hot Reduction → GF(3) → Efficient Index
```

## One-Hot Keyspace Reduction

### Problem: Exponential Keyspace

```
Thread ID space: 2^128 (UUID)
One-hot encoding: 128 bits
Behavior space: Intractable
```

### Solution: Reduce to GF(3) Trits

```
One-hot(128 bits) → Hash(64 bits) → SplitMix64 → Hue(360°) → Trit(-1,0,+1)

Keyspace: 3 states per trit
3 PLR ops × 3 trits = 9 behavior classes
Sufficient for:
  - User illusion (perceived control)
  - Behavior indexing (O(1) lookup)
  - Action field growth (bounded expansion)
```

## PLR → Trit Mapping

| PLR Op | Color Δ | Trit | Behavior |
|--------|---------|------|----------|
| **P** (Parallel) | Hue ±15° | 0 | ERGODIC: local exploration |
| **L** (Leading) | L ±10 | -1 | MINUS: constraint/validation |
| **R** (Relative) | C ±20, H ±30° | +1 | PLUS: expansion/generation |

### GF(3) Conservation

Every PLR sequence of length 3 sums to 0 (mod 3):

```
P L R = 0 + (-1) + 1 = 0 ✓
R R R = 1 + 1 + 1 = 3 ≡ 0 ✓
L P R = -1 + 0 + 1 = 0 ✓
```

## Thread ID to First Color

```python
def thread_to_color(thread_id: str) -> dict:
    """Extract color from thread identifier."""
    uuid_part = thread_id.replace("T-", "").replace("-", "")
    seed = int(uuid_part[:16], 16)
    _, val = splitmix64(seed)
    
    L = 10.0 + 85.0 * ((val & 0xFFFF) / 65535.0)
    C = 100.0 * (((val >> 16) & 0xFFFF) / 65535.0)
    H = 360.0 * (((val >> 32) & 0xFFFF) / 65535.0)
    trit = hue_to_trit(H)
    
    return {"thread_id": 