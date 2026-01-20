#!/usr/bin/env python3
"""
triad_interleave.py - Three-stream interleaving with GF(3) conservation

Usage:
    python triad_interleave.py [seed] [n_triplets] [policy]
    
Examples:
    python triad_interleave.py 0x42D 10 round_robin
    python triad_interleave.py 0x42D 10 gf3_balanced
    python triad_interleave.py 0xf061ebbc2ca74d78 5  # SPI canonical seed
"""
from dataclasses import dataclass, field
from typing import List, Literal
import hashlib
import math

# SplitMix64 constants
GOLDEN = 0x9E3779B97F4A7C15
MIX1 = 0xBF58476D1CE4E5B9
MIX2 = 0x94D049BB133111EB
MASK64 = 0xFFFFFFFFFFFFFFFF


@dataclass
class ColorEntry:
    """Single color entry in the schedule."""
    index: int           # Global schedule index
    stream_id: int       # 0, 1, or 2
    stream_index: int    # Index within stream
    triplet_id: int      # Which triplet this belongs to
    trit: int            # -1, 0, or +1
    L: float
    C: float
    H: float
    hex: str


@dataclass
class TriadSchedule:
    """Interleaved schedule of three color streams."""
    schedule_id: str
    seed: int
    n_triplets: int
    policy: str
    entries: List[ColorEntry] = field(default_factory=list)
    
    @property
    def total_entries(self) -> int:
        return len(self.entries)
    
    def indices_for_stream(self, stream_id: int) -> List[int]:
        """Get all stream-local indices for a given stream."""
        return [e.stream_index for e in self.entries if e.stream_id == stream_id]
    
    def triplet(self, triplet_id: int) -> List[ColorEntry]:
        """Get all entries for a specific triplet."""
        return [e for e in self.entries if e.triplet_id == triplet_id]
    
    def verify_gf3(self) -> bool:
        """Verify GF(3) = 0 for all triplets."""
        for tid in range(self.n_triplets):
            triplet = self.triplet(tid)
            if len(triplet) == 3:
                trit_sum = sum(e.trit for e in triplet)
                if trit_sum % 3 != 0:
                    return False
        return True
    
    def to_edn(self) -> str:
        """Export schedule as EDN."""
        entries_edn = []
        for e in self.entries:
            entries_edn.append(
                f'  {{:index {e.index} :stream {e.stream_id} '
                f':triplet {e.triplet_id} :trit {e.trit} '
                f':hex "{e.hex}" :L {e.L:.1f} :C {e.C:.1f} :H {e.H:.1f}}}'
            )
        return f'''{{:schedule-id "{self.schedule_id}"
 :seed {hex(self.seed)}
 :n-triplets {self.n_triplets}
 :policy :{self.policy.replace("_", "-")}
 :gf3-conserved {str(self.verify_gf3()).lower()}
 :entries [
{chr(10).join(entries_edn)}
 ]}}'''


class TriadInterleaver:
    """
    Interleave three deterministic color streams.
    
    Policies:
    - round_robin: Stream 0, 1, 2, 0, 1, 2, ...
    - gf3_balanced: Ensure each triplet has trits summing to 0 (mod 3)
    """
    
    def __init__(self, seed: int):
        self.seed = seed
        self.states = [
            (seed + GOLDEN * 0) & MASK64,  # Stream 0 (MINUS)
            (seed + GOLDEN * 1) & MASK64,  # Stream 1 (ERGODIC)
            (seed + GOLDEN * 2) & MASK64,  # Stream 2 (PLUS)
        ]
        self.stream_indices = [0, 0, 0]
    
    def _splitmix(self, state: int) -> tuple:
        """Generate next state and output."""
        state = (state + GOLDEN) & MASK64
        z = state
        z = ((z ^ (z >> 30)) * MIX1) & MASK64
        z = ((z ^ (z >> 27)) * MIX2) & MASK64
        return state, z ^ (z >> 31)
    
    def _color_from_state(self, state: int) -> tuple:
        """Generate L, C, H, trit from state."""
        s1, z1 = self._splitmix(state)
        s2, z2 = self._splitmix(s1)
        _, z3 = self._splitmix(s2)
        
        L = 10 + (z1 / MASK64) * 85
        C = (z2 / MASK64) * 100
        H = (z3 / MASK64) * 360
        
        # Trit from hue angle (GF(3) from color wheel)
        if H < 60 or H >= 300:
            trit = 1   # PLUS (warm)
        elif H < 180:
            trit = 0   # ERGODIC (green/cyan)
        else:
            trit = -1  # MINUS (cool)
        
        return L, C, H, trit, s2
    
    def _oklch_to_hex(self, L: float, C: float, H: float) -> str:
        """Convert OkLCH to hex."""
        a = C/100 * math.cos(math.radians(H))
        b = C/100 * math.sin(math.radians(H))
        
        l_ = L/100 + 0.3963377774 * a + 0.2158037573 * b
        m_ = L/100 - 0.1055613458 * a - 0.0638541728 * b
        s_ = L/100 - 0.0894841775 * a - 1.2914855480 * b
        
        l, m, s = max(0, l_)**3, max(0, m_)**3, max(0, s_)**3
        
        r = max(0, min(1, +4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s))
        g = max(0, min(1, -1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s))
        b = max(0, min(1, -0.0041960863 * l - 0.7034186147 * m + 1.7076147010 * s))
        
        return f"#{int(r*255):02X}{int(g*255):02X}{int(b*255):02X}"
    
    def next_from_stream(self, stream_id: int) -> ColorEntry:
        """Get next color from specified stream."""
        L, C, H, trit, new_state = self._color_from_state(self.states[stream_id])
        self.states[stream_id] = new_state
        
        entry = ColorEntry(
            index=-1,
            stream_id=stream_id,
            stream_index=self.stream_indices[stream_id],
            triplet_id=-1,
            trit=trit,
            L=L, C=C, H=H,
            hex=self._oklch_to_hex(L, C, H)
        )
        self.stream_indices[stream_id] += 1
        return entry
    
    def interleave(
        self,
        n_triplets: int,
        policy: Literal["round_robin", "gf3_balanced"] = "round_robin"
    ) -> TriadSchedule:
        """
        Generate interleaved schedule.
        
        Args:
            n_triplets: Number of triplets to generate
            policy: Scheduling policy
        
        Returns:
            TriadSchedule with all entries
        """
        schedule_id = hashlib.sha256(
            f"{self.seed}:{n_triplets}:{policy}".encode()
        ).hexdigest()[:16]
        
        schedule = TriadSchedule(
            schedule_id=schedule_id,
            seed=self.seed,
            n_triplets=n_triplets,
            policy=policy
        )
        
        global_index = 0
        
        if policy == "gf3_balanced":
            # Pre-generate pools for each trit value
            # Keep generating until we have enough of each
            pools = {-1: [], 0: [], 1: []}
            stream_cycle = 0
            
            while min(len(pools[-1]), len(pools[0]), len(pools[1])) < n_triplets:
                stream_id = stream_cycle % 3
                entry = self.next_from_stream(stream_id)
                pools[entry.trit].append(entry)
                stream_cycle += 1
            
            # Now form balanced triplets: one from each pool
            for triplet_id in range(n_triplets):
                triplet_entries = [
                    pools[-1][triplet_id],
                    pools[0][triplet_id],
                    pools[1][triplet_id]
                ]
                for entry in triplet_entries:
                    entry.index = global_index
                    entry.triplet_id = triplet_id
                    schedule.entries.append(entry)
                    global_index += 1
        else:
            # Round robin: 0, 1, 2
            for triplet_id in range(n_triplets):
                for stream_id in [0, 1, 2]:
                    entry = self.next_from_stream(stream_id)
                    entry.index = global_index
                    entry.triplet_id = triplet_id
                    schedule.entries.append(entry)
                    global_index += 1
        
        return schedule


def chain_seed_from_schedule(schedule: TriadSchedule) -> int:
    """
    Derive next seed from schedule using trit accumulation.
    Integrates with unworld's derivational chain approach.
    """
    trit_sum = sum(e.trit for e in schedule.entries)
    direction = trit_sum % 3
    if direction == 2:
        direction = -1
    
    new_state = (schedule.seed + direction * GOLDEN) & MASK64
    interleaver = TriadInterleaver(0)
    _, next_seed = interleaver._splitmix(new_state)
    
    return next_seed


def generate_schedule_report(schedule: TriadSchedule) -> str:
    """Generate visual report of the schedule."""
    gf3_ok = schedule.verify_gf3()
    
    report = f"""
╔═══════════════════════════════════════════════════════════════════╗
║  TRIAD INTERLEAVE SCHEDULE                                        ║
╚═══════════════════════════════════════════════════════════════════╝

Schedule ID: {schedule.schedule_id}
Seed: {hex(schedule.seed)}
Triplets: {schedule.n_triplets}
Policy: {schedule.policy}
GF(3) Conserved: {"YES" if gf3_ok else "NO"}

--- Stream Visualization ---
"""
    
    stream_chars = {0: "M", 1: "E", 2: "P"}  # MINUS, ERGODIC, PLUS
    
    for stream_id in [0, 1, 2]:
        stream_entries = [e for e in schedule.entries if e.stream_id == stream_id]
        line = f"  Stream {stream_id} ({['MINUS','ERGODIC','PLUS'][stream_id]}): "
        for e in stream_entries[:12]:
            line += f"{stream_chars[stream_id]}-"
        if len(stream_entries) > 12:
            line += "..."
        report += line + "\n"
    
    report += "\n--- Interleaved (first 12 entries) ---\n"
    for e in schedule.entries[:12]:
        trit_char = {-1: "-", 0: "0", 1: "+"}[e.trit]
        report += f"  [{e.index:3d}] S{e.stream_id} T{e.triplet_id} "
        report += f"trit={trit_char} {e.hex} L={e.L:5.1f} C={e.C:5.1f} H={e.H:5.1f}\n"
    
    report += "\n--- Triplet Verification ---\n"
    for tid in range(min(4, schedule.n_triplets)):
        triplet = schedule.triplet(tid)
        trits = [e.trit for e in triplet]
        trit_sum = sum(trits)
        status = "OK" if trit_sum % 3 == 0 else "FAIL"
        report += f"  Triplet {tid}: trits={trits} sum={trit_sum} [{status}]\n"
    
    # Seed chain
    next_seed = chain_seed_from_schedule(schedule)
    report += f"\n--- Unworld Seed Chain ---\n"
    report += f"  Current: {hex(schedule.seed)}\n"
    report += f"  Next:    {hex(next_seed)}\n"
    
    return report


if __name__ == "__main__":
    import sys
    
    # Parse arguments
    seed = int(sys.argv[1], 16) if len(sys.argv) > 1 else 0x42D
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    policy = sys.argv[3] if len(sys.argv) > 3 else "round_robin"
    
    # Generate schedule
    interleaver = TriadInterleaver(seed)
    schedule = interleaver.interleave(n, policy)
    
    # Output
    if "--edn" in sys.argv:
        print(schedule.to_edn())
    else:
        print(generate_schedule_report(schedule))
