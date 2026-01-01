# PLR Thread Coloring: Full Implementations

Complete implementations of PLR thread coloring with one-hot reduction to GF(3).

## Python Implementation

```python
#!/usr/bin/env python3
"""PLR Thread Coloring with One-Hot Reduction"""

import hashlib
from typing import Tuple, Dict, List

GOLDEN = 0x9E3779B97F4A7C15
MASK64 = 0xFFFFFFFFFFFFFFFF

def splitmix64(seed: int) -> Tuple[int, int]:
    seed = (seed + GOLDEN) & MASK64
    z = seed
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    return seed, (z ^ (z >> 31)) & MASK64

def hue_to_trit(h: float) -> int:
    h = h % 360
    if h < 60 or h >= 300:
        return 1   # PLUS (warm)
    elif h < 180:
        return 0   # ERGODIC (neutral)
    else:
        return -1  # MINUS (cold)

def thread_to_color(thread_id: str) -> Dict:
    """First color from thread ID."""
    uuid_clean = thread_id.replace("T-", "").replace("-", "")
    seed = int(uuid_clean[:16], 16) if len(uuid_clean) >= 16 else hash(thread_id)
    
    _, val = splitmix64(seed & MASK64)
    
    L = 10.0 + 85.0 * ((val & 0xFFFF) / 65535.0)
    C = 100.0 * (((val >> 16) & 0xFFFF) / 65535.0)
    H = 360.0 * (((val >> 32) & 0xFFFF) / 65535.0)
    trit = hue_to_trit(H)
    
    return {"thread_id": thread_id, "seed": seed, "L": L, "C": C, "H": H, "trit": trit}

# PLR operations
def P(color: Dict, direction: int = 1) -> Dict:
    return {**color, "H": (color["H"] + 15 * direction) % 360, "op_trit": 0}

def L(color: Dict, direction: int = 1) -> Dict:
    return {**color, "L": max(1, min(99, color["L"] + 10 * direction)), "op_trit": -1}

def R(color: Dict, direction: int = 1) -> Dict:
    return {
        **color,
        "C": max(0, min(150, color["C"] + 20 * direction)),
        "H": (color["H"] + 30 * direction) % 360,
        "op_trit": 1
    }

def apply_plr_sequence(color: Dict, sequence: str) -> List[Dict]:
    """Apply PLR sequence, return color path."""
    ops = {"P": P, "L": L, "R": R}
    path = [color]
    current = color
    for op in sequence:
        if op in ops:
            current = ops[op](current)
            path.append(current)
    return path

def behavior_class(color: Dict, last_op_trit: int = 0) -> int:
    """Compute 9-class behavior index."""
    base_trit = color["trit"]  # -1, 0, +1
    op_idx = {-1: 0, 0: 1, 1: 2}[last_op_trit]  # L, P, R
    trit_idx = {-1: 0, 0: 1, 1: 2}[base_trit]
    return op_idx * 3 + trit_idx

BEHAVIOR_NAMES = [
    "L-MINUS: contract", "L-ERGODIC: adjust", "L-PLUS: brighten",
    "P-MINUS: validate", "P-ERGODIC: explore", "P-PLUS: expand",
    "R-MINUS: simplify", "R-ERGODIC: modulate", "R-PLUS: elaborate"
]

# Demo
if __name__ == "__main__":
    thread = "T-019b77f9-2cae-7661-bf9f-714d9c5e677c"
    color = thread_to_color(thread)
    print(f"Thread: {thread}")
    print(f"First Color: L={color['L']:.1f} C={color['C']:.1f} H={color['H']:.1f}")
    print(f"Trit: {color['trit']} ({['MINUS','ERGODIC','PLUS'][color['trit']+1]})")
    
    # PLR path
    path = apply_plr_sequence(color, "PLR")
    print("\nPLR Path:")
    for i, c in enumerate(path):
        print(f"  {i}: L={c['L']:.1f} C={c['C']:.1f} H={c['H']:.1f}")
```

## Julia Implementation

```julia
module PLRThreadColoring

export thread_to_color, P, L, R, apply_sequence, behavior_class

const GOLDEN = 0x9E3779B97F4A7C15
const MIX1 = 0xBF58476D1CE4E5B9
const MIX2 = 0x94D049BB133111EB

function splitmix64(seed::UInt64)
    seed += GOLDEN
    z = seed
    z = (z ⊻ (z >> 30)) * MIX1
    z = (z ⊻ (z >> 27)) * MIX2
    (seed, z ⊻ (z >> 31))
end

function hue_to_trit(h::Float64)::Int8
    h = mod(h, 360)
    if h < 60 || h >= 300
        Int8(1)   # PLUS
    elseif h < 180
        Int8(0)   # ERGODIC
    else
        Int8(-1)  # MINUS
    end
end

function thread_to_color(thread_id::String)
    uuid_clean = replace(replace(thread_id, "T-" => ""), "-" => "")
    seed = parse(UInt64, uuid_clean[1:min(16, length(uuid_clean))], base=16)
    
    _, val = splitmix64(seed)
    
    L = 10.0 + 85.0 * ((val & 0xFFFF) / 65535.0)
    C = 100.0 * (((val >> 16) & 0xFFFF) / 65535.0)
    H = 360.0 * (((val >> 32) & 0xFFFF) / 65535.0)
    trit = hue_to_trit(H)
    
    (thread_id=thread_id, seed=seed, L=L, C=C, H=H, trit=trit)
end

# PLR Operations
P(c; direction=1) = (L=c.L, C=c.C, H=mod(c.H + 15*direction, 360), trit=c.trit, op=:P)
L(c; direction=1) = (L=clamp(c.L + 10*direction, 1, 99), C=c.C, H=c.H, trit=c.trit, op=:L)
R(c; direction=1) = (L=c.L, C=clamp(c.C + 20*direction, 0, 150), 
                     H=mod(c.H + 30*direction, 360), trit=c.trit, op=:R)

function apply_sequence(color, ops::String)
    path = [color]
    current = color
    for op in ops
        current = if op == 'P'
            P(current)
        elseif op == 'L'
            L(current)
        elseif op == 'R'
            R(current)
        else
            current
        end
        push!(path, current)
    end
    path
end

function behavior_class(trit::Int8, op_trit::Int8)::Int
    op_idx = Dict(-1 => 0, 0 => 1, 1 => 2)[op_trit]
    trit_idx = Dict(-1 => 0, 0 => 1, 1 => 2)[trit]
    op_idx * 3 + trit_idx
end

end
```

## Field Capacity Growth

```julia
mutable struct PerceptionActionField
    capacity::Float64
    plr_history::Vector{Symbol}
    color_memory::Dict{String, NamedTuple}
end

function PerceptionActionField()
    PerceptionActionField(1.0, Symbol[], Dict())
end

function perceive!(field::PerceptionActionField, thread_id::String)
    color = thread_to_color(thread_id)
    field.color_memory[thread_id] = color
    
    # Perception expands field proportional to color diversity
    if length(field.color_memory) > 1
        colors = values(field.color_memory)
        hue_std = std([c.H for c in colors])
        field.capacity *= (1 + 0.01 * hue_std / 360)
    end
    
    color
end

function act!(field::PerceptionActionField, plr_op::Symbol)
    push!(field.plr_history, plr_op)
    
    # Action expands field proportional to PLR diversity
    recent = field.plr_history[max(1, end-9):end]
    diversity = length(unique(recent)) / 3.0
    field.capacity *= (1 + 0.05 * diversity)
    
    field.capacity
end
```

## DuckDB Behavior Index

```sql
CREATE TABLE thread_behaviors (
    thread_id TEXT PRIMARY KEY,
    seed BIGINT NOT NULL,
    first_color_hex TEXT,
    first_color_L DOUBLE,
    first_color_C DOUBLE,
    first_color_H DOUBLE,
    base_trit INTEGER CHECK (base_trit IN (-1, 0, 1)),
    plr_sequence TEXT,
    behavior_class INTEGER,  -- 0-8 for 9-class system
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX idx_behavior ON thread_behaviors(behavior_class);
CREATE INDEX idx_trit ON thread_behaviors(base_trit);

-- Efficient behavior lookup
SELECT * FROM thread_behaviors 
WHERE behavior_class = (SELECT behavior_class FROM classify_thread(?));
```

## User Illusion Framework

The user perceives control while the system operates on reduced state:

```lisp
(plr-thread-coloring
  :gf3-conservation
  (lambda (sequence)
    (zerop (mod (reduce #'+ (mapcar #'plr-trit sequence)) 3)))
  
  :user-illusion
  (lambda (one-hot-input)
    "User provides 128-bit thread ID.
     System reduces to 1.58-bit trit.
     User perceives rich color space.
     System uses 9-class behavior index.")
  
  :field-growth
  ((perception . (lambda (field thread) (* (field-capacity field) 
                                            (+ 1 (* 0.01 (color-diversity field))))))
   (action . (lambda (field plr-op) (* (field-capacity field) 
                                        (+ 1 (* 0.05 (plr-diversity field))))))))
```
