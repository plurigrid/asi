#!/usr/bin/env python3
"""
PLR Thread Coloring: One-Hot Keyspace Reduction for Behavior Indexing

Maps thread identifiers to colors via PLR (Parallel/Leading-tone/Relative)
transformations. Reduces 128-bit one-hot space to 3-state GF(3) trits.

Seed: 1069 (zubuyul)
"""

import hashlib
import math
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
from collections import Counter

# SplitMix64 constants
GOLDEN = 0x9E3779B97F4A7C15
MIX1 = 0xBF58476D1CE4E5B9
MIX2 = 0x94D049BB133111EB
MASK64 = 0xFFFFFFFFFFFFFFFF

ZUBUYUL = 1069


def splitmix64(seed: int) -> Tuple[int, int]:
    """SplitMix64 PRNG - deterministic and splittable."""
    seed = (seed + GOLDEN) & MASK64
    z = seed
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    return seed, (z ^ (z >> 31)) & MASK64


def hue_to_trit(h: float) -> int:
    """Map hue (0-360) to GF(3) trit."""
    h = h % 360
    if h < 60 or h >= 300:
        return 1   # PLUS (warm: red/orange/magenta)
    elif h < 180:
        return 0   # ERGODIC (neutral: yellow/green/cyan)
    else:
        return -1  # MINUS (cold: blue/purple)


def oklch_to_hex(L: float, C: float, H: float) -> str:
    """Convert OkLCH to hex color string."""
    # Simplified OkLCH → RGB conversion
    h_rad = math.radians(H)
    a = C * 0.01 * math.cos(h_rad)
    b = C * 0.01 * math.sin(h_rad)
    l = L / 100.0
    
    # OkLab → Linear RGB (approximate)
    l_ = l + 0.3963377774 * a + 0.2158037573 * b
    m_ = l - 0.1055613458 * a - 0.0638541728 * b
    s_ = l - 0.0894841775 * a - 1.2914855480 * b
    
    l3, m3, s3 = l_**3, m_**3, s_**3
    
    r = +4.0767416621 * l3 - 3.3077115913 * m3 + 0.2309699292 * s3
    g = -1.2684380046 * l3 + 2.6097574011 * m3 - 0.3413193965 * s3
    b_val = -0.0041960863 * l3 - 0.7034186147 * m3 + 1.7076147010 * s3
    
    def clamp_byte(x): return max(0, min(255, int(x * 255)))
    return f"#{clamp_byte(r):02X}{clamp_byte(g):02X}{clamp_byte(b_val):02X}"


@dataclass
class ThreadColor:
    """Color derived from thread identifier."""
    thread_id: str
    seed: int
    L: float  # Lightness (0-100)
    C: float  # Chroma (0-150)
    H: float  # Hue (0-360)
    trit: int  # GF(3): -1, 0, +1
    
    @property
    def hex(self) -> str:
        return oklch_to_hex(self.L, self.C, self.H)
    
    @property
    def role(self) -> str:
        return {-1: "MINUS", 0: "ERGODIC", 1: "PLUS"}[self.trit]
    
    def to_sexp(self) -> str:
        return f'(thread-color :id "{self.thread_id}" :L {self.L:.1f} :C {self.C:.1f} :H {self.H:.1f} :trit {self.trit})'


def thread_to_color(thread_id: str) -> ThreadColor:
    """
    Convert thread ID to its FIRST color.
    The first color IS the thread's identity.
    """
    # Clean UUID
    uuid_clean = thread_id.replace("T-", "").replace("-", "")
    
    # Parse seed from first 16 hex chars
    if len(uuid_clean) >= 16:
        seed = int(uuid_clean[:16], 16)
    else:
        # Fallback: hash the thread ID
        seed = int(hashlib.sha256(thread_id.encode()).hexdigest()[:16], 16)
    
    # SplitMix64 for deterministic value
    _, val = splitmix64(seed & MASK64)
    
    # Extract LCH components from 64-bit value
    L = 10.0 + 85.0 * ((val & 0xFFFF) / 65535.0)
    C = 100.0 * (((val >> 16) & 0xFFFF) / 65535.0)
    H = 360.0 * (((val >> 32) & 0xFFFF) / 65535.0)
    trit = hue_to_trit(H)
    
    return ThreadColor(thread_id=thread_id, seed=seed, L=L, C=C, H=H, trit=trit)


# =============================================================================
# PLR Operations
# =============================================================================

def P(color: ThreadColor, direction: int = 1) -> ThreadColor:
    """
    Parallel transformation: Hue ±15°
    Preserves L and C (2/3 common tones).
    Op trit: 0 (ERGODIC)
    """
    new_H = (color.H + 15 * direction) % 360
    new_trit = hue_to_trit(new_H)
    return ThreadColor(
        thread_id=color.thread_id,
        seed=color.seed,
        L=color.L, C=color.C, H=new_H,
        trit=new_trit
    )


def L(color: ThreadColor, direction: int = 1) -> ThreadColor:
    """
    Leading-tone transformation: Lightness ±10
    Preserves C and H (2/3 common tones).
    Op trit: -1 (MINUS)
    """
    new_L = max(1.0, min(99.0, color.L + 10 * direction))
    return ThreadColor(
        thread_id=color.thread_id,
        seed=color.seed,
        L=new_L, C=color.C, H=color.H,
        trit=color.trit
    )


def R(color: ThreadColor, direction: int = 1) -> ThreadColor:
    """
    Relative transformation: Chroma ±20, Hue ±30°
    Largest shift (only L preserved).
    Op trit: +1 (PLUS)
    """
    new_C = max(0.0, min(150.0, color.C + 20 * direction))
    new_H = (color.H + 30 * direction) % 360
    new_trit = hue_to_trit(new_H)
    return ThreadColor(
        thread_id=color.thread_id,
        seed=color.seed,
        L=color.L, C=new_C, H=new_H,
        trit=new_trit
    )


PLR_OPS = {"P": P, "L": L, "R": R}
PLR_TRITS = {"P": 0, "L": -1, "R": 1}


def apply_plr_sequence(color: ThreadColor, sequence: str) -> List[ThreadColor]:
    """Apply PLR sequence, return color path."""
    path = [color]
    current = color
    for op in sequence.upper():
        if op in PLR_OPS:
            current = PLR_OPS[op](current)
            path.append(current)
    return path


# =============================================================================
# Behavior Indexing (9-class system)
# =============================================================================

BEHAVIOR_CLASSES = {
    0: "L-MINUS: contract/validate",
    1: "L-ERGODIC: adjust/balance",
    2: "L-PLUS: brighten/expand",
    3: "P-MINUS: local-validate",
    4: "P-ERGODIC: local-explore",
    5: "P-PLUS: local-expand",
    6: "R-MINUS: simplify/reduce",
    7: "R-ERGODIC: modulate/shift",
    8: "R-PLUS: elaborate/generate",
}


def behavior_class(color_trit: int, op_trit: int) -> int:
    """
    Compute 9-class behavior index.
    
    Args:
        color_trit: Base trit from thread color (-1, 0, +1)
        op_trit: PLR operation trit (L=-1, P=0, R=+1)
    
    Returns:
        Behavior class 0-8
    """
    op_idx = {-1: 0, 0: 1, 1: 2}[op_trit]
    trit_idx = {-1: 0, 0: 1, 1: 2}[color_trit]
    return op_idx * 3 + trit_idx


def classify_thread(thread_id: str, last_plr: str = "P") -> Tuple[int, str]:
    """Classify thread behavior from ID and last PLR operation."""
    color = thread_to_color(thread_id)
    op_trit = PLR_TRITS.get(last_plr.upper(), 0)
    cls = behavior_class(color.trit, op_trit)
    return cls, BEHAVIOR_CLASSES[cls]


# =============================================================================
# One-Hot Reduction
# =============================================================================

def one_hot_to_gf3(one_hot: List[int]) -> int:
    """
    Reduce one-hot encoding (128 bits) to GF(3) trit.
    
    This is the key efficiency gain:
    - Input: 2^128 possible states
    - Output: 3 possible states
    - Reduction: 128 bits → 1.58 bits
    """
    # Convert one-hot to integer
    value = sum(bit << i for i, bit in enumerate(one_hot))
    
    # Hash to 64-bit seed
    seed = value & MASK64
    
    # SplitMix64 to get deterministic value
    _, val = splitmix64(seed)
    
    # Extract hue and map to trit
    H = 360.0 * ((val >> 32) & 0xFFFF) / 65535.0
    return hue_to_trit(H)


# =============================================================================
# Perception/Action Field
# =============================================================================

@dataclass
class PerceptionActionField:
    """
    Growing information field through PLR navigation.
    
    The field capacity grows as the user explores more diverse
    color paths, creating sufficient illusion of agency.
    """
    seed: int = ZUBUYUL
    capacity: float = 1.0
    plr_history: List[str] = field(default_factory=list)
    color_memory: Dict[str, ThreadColor] = field(default_factory=dict)
    
    def perceive(self, thread_id: str) -> Dict:
        """
        User perceives thread as colored behavior.
        Perception expands field proportional to color diversity.
        """
        color = thread_to_color(thread_id)
        self.color_memory[thread_id] = color
        
        # Expand capacity based on color diversity
        if len(self.color_memory) > 1:
            hues = [c.H for c in self.color_memory.values()]
            # Circular standard deviation for hue
            mean_sin = sum(math.sin(math.radians(h)) for h in hues) / len(hues)
            mean_cos = sum(math.cos(math.radians(h)) for h in hues) / len(hues)
            R = math.sqrt(mean_sin**2 + mean_cos**2)
            circ_var = 1 - R  # 0 = all same, 1 = max spread
            self.capacity *= (1 + 0.02 * circ_var)
        
        behavior_cls, behavior_name = classify_thread(thread_id)
        
        return {
            "thread_id": thread_id,
            "color": color.hex,
            "trit": color.trit,
            "role": color.role,
            "behavior_class": behavior_cls,
            "behavior_name": behavior_name,
            "field_capacity": self.capacity
        }
    
    def act(self, plr_op: str) -> float:
        """
        User action (PLR choice) expands field capacity.
        Diversity of recent actions → faster growth.
        """
        self.plr_history.append(plr_op.upper())
        
        # Compute diversity of last 10 operations
        recent = self.plr_history[-10:]
        diversity = len(set(recent)) / 3.0  # 0.33 to 1.0
        
        # Expand capacity
        self.capacity *= (1 + 0.05 * diversity)
        
        return self.capacity
    
    def sufficiency(self) -> Dict:
        """
        Measure sufficiency of user illusion.
        
        Sufficiency = capacity × coverage × diversity
        """
        coverage = min(1.0, len(self.color_memory) / 10)  # 10 threads = full coverage
        
        if self.plr_history:
            counts = Counter(self.plr_history)
            total = sum(counts.values())
            probs = [c / total for c in counts.values()]
            entropy = -sum(p * math.log2(p) for p in probs if p > 0)
            diversity = entropy / math.log2(3)  # Normalize to [0, 1]
        else:
            diversity = 0
        
        sufficiency = self.capacity * coverage * max(0.1, diversity)
        
        return {
            "capacity": self.capacity,
            "coverage": coverage,
            "diversity": diversity,
            "sufficiency": sufficiency,
            "is_sufficient": sufficiency > 1.0
        }


# =============================================================================
# Demo
# =============================================================================

def demo():
    """Demonstrate PLR Thread Coloring."""
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  PLR THREAD COLORING                                         ║")
    print("║  One-Hot → GF(3) | Behavior Indexing | Field Capacity        ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()
    
    # Current thread
    thread = "T-019b77f9-2cae-7661-bf9f-714d9c5e677c"
    color = thread_to_color(thread)
    
    print("─── Thread → First Color ───")
    print(f"  Thread: {thread}")
    print(f"  Color:  {color.hex}")
    print(f"  LCH:    L={color.L:.1f} C={color.C:.1f} H={color.H:.1f}")
    print(f"  Trit:   {color.trit} ({color.role})")
    print()
    
    # PLR path
    print("─── PLR Transitions ───")
    path = apply_plr_sequence(color, "PLR")
    for i, c in enumerate(path):
        op = ["•", "P", "L", "R"][min(i, 3)]
        print(f"  {op}: {c.hex} L={c.L:.1f} C={c.C:.1f} H={c.H:.1f} [{c.role}]")
    
    # GF(3) sum
    path_trits = [c.trit for c in path]
    print(f"\n  GF(3) sum: {sum(path_trits)} (mod 3 = {sum(path_trits) % 3})")
    print()
    
    # Behavior classification
    print("─── 9-Class Behavior Index ───")
    for op in ["P", "L", "R"]:
        cls, name = classify_thread(thread, op)
        print(f"  {op}: class {cls} → {name}")
    print()
    
    # One-hot reduction demo
    print("─── One-Hot Reduction ───")
    one_hot = [1 if i == 42 else 0 for i in range(128)]
    trit = one_hot_to_gf3(one_hot)
    print(f"  One-hot[42] (128 bits) → trit {trit}")
    print(f"  Reduction: 2^128 states → 3 states")
    print(f"  Bits: 128 → {math.log2(3):.2f}")
    print()
    
    # Perception/Action Field
    print("─── Perception/Action Field ───")
    field_obj = PerceptionActionField()
    
    threads = [
        "T-019b77f9-2cae-7661-bf9f-714d9c5e677c",
        "T-019b77ec-fe28-74c9-8b57-3782447998c3",
        "T-3f1beb2b-bded-4fda-96cc-1af7192f24b6",
    ]
    
    for t in threads:
        result = field_obj.perceive(t)
        print(f"  Perceive {t[:20]}... → {result['role']}")
    
    for op in ["P", "L", "R", "P", "R"]:
        cap = field_obj.act(op)
        print(f"  Act {op} → capacity = {cap:.3f}")
    
    suff = field_obj.sufficiency()
    print(f"\n  Sufficiency: {suff['sufficiency']:.3f}")
    print(f"  Is sufficient: {suff['is_sufficient']}")


if __name__ == "__main__":
    demo()
