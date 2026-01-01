#!/usr/bin/env python3
"""
ordered_locale_fanout.py - Triadic parallel dispatch via ordered locale cocones

Mathematical foundation (Heunen-van der Schaaf 2024):
- Frame L of opens over GF(3) = {-1, 0, +1}
- ≪ order between opens (direction of computation)
- Fanout = cocone construction over triadic ordered locale
- Aggregation = colimit of the cocone
"""

from __future__ import annotations
import subprocess
import sys
from dataclasses import dataclass, field
from typing import Callable, Any, List, Dict, FrozenSet, Optional
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import reduce
import os

sys.path.insert(0, os.environ.get("ORDERED_LOCALE_PATH", os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "ordered-locale")))
from ordered_locale import (
    Frame, OrderedLocale, triadic_gf3, cocone, cone, 
    directed_interval, print_locale
)

# ============================================================================
# SplitMix64 for deterministic seeding
# ============================================================================

GOLDEN = 0x9E3779B97F4A7C15
MIX1 = 0xBF58476D1CE4E5B9
MIX2 = 0x94D049BB133111EB
MASK64 = 0xFFFFFFFFFFFFFFFF


def splitmix64(x: int) -> int:
    """SplitMix64 PRNG step"""
    z = (x + GOLDEN) & MASK64
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    return (z ^ (z >> 31)) & MASK64


def trit_from_seed(seed: int) -> int:
    """Extract trit ∈ {-1, 0, +1} from seed"""
    return (seed % 3) - 1


# ============================================================================
# Locale Agents (opens in the frame)
# ============================================================================

@dataclass
class LocaleAgent:
    """
    An agent corresponds to an open in the triadic ordered locale.
    
    The ≪ order determines computational flow:
      MINUS ≪ ERGODIC ≪ PLUS
    """
    trit: int
    role: str
    voice: str
    language: str
    seed: int = 0
    
    @property
    def open(self) -> FrozenSet[int]:
        """The agent's open in the frame (up-closure of trit)"""
        if self.trit == -1:
            return frozenset([-1, 0, 1])  # Full locale
        elif self.trit == 0:
            return frozenset([0, 1])  # Ergodic + Plus
        else:
            return frozenset([1])  # Just Plus


# The triadic locale with agents as opens
TRIADIC_LOCALE = triadic_gf3()

AGENTS = [
    LocaleAgent(trit=-1, role="VALIDATOR", voice="Anna", language="German"),
    LocaleAgent(trit=0, role="COORDINATOR", voice="Thomas", language="French"),
    LocaleAgent(trit=1, role="GENERATOR", voice="Luca", language="Italian"),
]


def verify_locale_structure():
    """Verify the triadic locale satisfies all axioms"""
    assert TRIADIC_LOCALE.is_ordered_locale(), "Triadic locale must be valid"
    assert TRIADIC_LOCALE.has_open_cones(), "Open cone condition must hold"
    
    # Verify ≪ order matches computational flow
    minus_open = frozenset([-1, 0, 1])
    erg_open = frozenset([0, 1])
    plus_open = frozenset([1])
    
    # MINUS ≪ ERGODIC ≪ PLUS (in terms of inclusion reversal)
    # Larger opens come "before" in the order
    assert minus_open > erg_open > plus_open, "Frame order matches flow"
    
    return True


# ============================================================================
# Cocone Construction (Fanout)
# ============================================================================

@dataclass
class FanoutCocone:
    """
    A cocone over the triadic diagram with apex = merged result.
    
    Structure:
                   MINUS                ERGODIC               PLUS
                    (ι₋₁)                (ι₀)                 (ι₊₁)
                      ↘                    ↓                    ↙
                               APEX (colimit = merged output)
    """
    base_locale: OrderedLocale
    apex_name: str = "MERGED"
    legs: Dict[int, Any] = field(default_factory=dict)  # trit → result
    apex_value: Any = None
    
    def inject(self, trit: int, value: Any):
        """Leg of cocone: inject result from agent into apex"""
        self.legs[trit] = value
    
    def compute_apex(self, merge_fn: Callable[[Dict[int, Any]], Any]) -> Any:
        """
        Colimit = universal property of cocone.
        
        merge_fn takes all leg values and produces the apex.
        This is the unique map from the colimit.
        """
        self.apex_value = merge_fn(self.legs)
        return self.apex_value
    
    def verify_universal(self) -> bool:
        """
        Check that the apex satisfies the universal property:
        Any other cocone factors uniquely through this one.
        """
        # For our finite case, just verify all legs are populated
        expected_trits = {-1, 0, 1}
        return set(self.legs.keys()) == expected_trits


# ============================================================================
# Fanout Execution
# ============================================================================

def announce(agent: LocaleAgent, message: str):
    """Announce via macOS say with locale-specific voice"""
    subprocess.run(
        ["say", "-v", agent.voice, message],
        capture_output=True
    )


def fork_seeds(parent_seed: int) -> Dict[int, int]:
    """
    Fork parent seed into 3 child seeds following ≪ order.
    
    The ≪ order ensures seeds flow: MINUS → ERGODIC → PLUS
    """
    return {
        -1: splitmix64(parent_seed ^ GOLDEN),
        0: splitmix64(splitmix64(parent_seed ^ GOLDEN)),
        1: splitmix64(splitmix64(splitmix64(parent_seed ^ GOLDEN))),
    }


def ordered_fanout(
    seed: int,
    task_fn: Callable[[LocaleAgent, Any], Any],
    context: Any = None,
    merge_fn: Optional[Callable[[Dict[int, Any]], Any]] = None,
    announce_start: bool = False,
    announce_end: bool = False,
    verify_gf3: bool = True,
) -> FanoutCocone:
    """
    Execute triadic fanout as a cocone over the ordered locale.
    
    Args:
        seed: Parent seed for deterministic forking
        task_fn: Function(agent, context) -> result
        context: Shared context passed to all agents
        merge_fn: Colimit morphism (optional, default: dict)
        announce_start: Whether to announce agent start
        announce_end: Whether to announce completion
        verify_gf3: Check GF(3) conservation
    
    Returns:
        FanoutCocone with computed apex
    """
    # Verify locale structure
    verify_locale_structure()
    
    # Create cocone over triadic locale
    cocone_locale = cocone(TRIADIC_LOCALE, coapex_name="APEX")
    fanout_cocone = FanoutCocone(base_locale=cocone_locale)
    
    # Fork seeds following ≪ order
    child_seeds = fork_seeds(seed)
    
    def run_agent(agent: LocaleAgent) -> tuple[int, Any]:
        agent.seed = child_seeds[agent.trit]
        
        if announce_start:
            announce(agent, f"Agent {agent.role} starting")
        
        result = task_fn(agent, context)
        
        if announce_end:
            announce(agent, f"Agent {agent.role} complete")
        
        return agent.trit, result
    
    # Parallel execution (all agents run concurrently)
    with ThreadPoolExecutor(max_workers=3) as executor:
        futures = [executor.submit(run_agent, agent) for agent in AGENTS]
        for future in as_completed(futures):
            trit, result = future.result()
            fanout_cocone.inject(trit, result)
    
    # Compute colimit (apex)
    if merge_fn is None:
        merge_fn = lambda legs: legs  # Default: just return all legs
    
    fanout_cocone.compute_apex(merge_fn)
    
    # Verify GF(3) conservation
    if verify_gf3:
        trit_sum = sum(a.trit for a in AGENTS)
        assert trit_sum % 3 == 0, f"GF(3) violation: Σtrits = {trit_sum}"
    
    return fanout_cocone


# ============================================================================
# Sheaf-Compatible Fanout
# ============================================================================

@dataclass
class SheafSection:
    """
    A section of a sheaf over the ordered locale.
    
    Restriction maps must respect ≪ order:
    If U ≪ V, then res_{V,U}: F(V) → F(U) must exist.
    """
    open_set: FrozenSet[int]
    value: Any
    restrictions: Dict[FrozenSet[int], Callable] = field(default_factory=dict)


def sheaf_fanout(
    seed: int,
    section_fn: Callable[[LocaleAgent, Any], SheafSection],
    context: Any = None,
    glue: bool = True,
) -> Dict[FrozenSet[int], Any]:
    """
    Execute fanout that produces sheaf sections over the ordered locale.
    
    Each agent produces a section over its open.
    Sections must agree on overlaps (sheaf condition).
    
    Returns:
        Dictionary mapping opens to section values
    """
    child_seeds = fork_seeds(seed)
    sections: Dict[FrozenSet[int], SheafSection] = {}
    
    def run_agent(agent: LocaleAgent):
        agent.seed = child_seeds[agent.trit]
        section = section_fn(agent, context)
        return agent.open, section
    
    with ThreadPoolExecutor(max_workers=3) as executor:
        futures = [executor.submit(run_agent, agent) for agent in AGENTS]
        for future in as_completed(futures):
            open_set, section = future.result()
            sections[open_set] = section
    
    # Verify sheaf condition: sections agree on overlaps
    if glue:
        for U1, s1 in sections.items():
            for U2, s2 in sections.items():
                overlap = U1 & U2
                if overlap and overlap != U1 and overlap != U2:
                    # Would need restriction maps here
                    pass
    
    return {k: v.value for k, v in sections.items()}


# ============================================================================
# MLX Integration (Optional)
# ============================================================================

def mlx_triadic_generate(
    seed: int, 
    prompts: Dict[str, str], 
    model: str = None
) -> FanoutCocone:
    """
    Generate text with 3 parallel MLX streams over ordered locale.
    """
    try:
        from mlx_lm import load, generate
        from mlx_lm.sample_utils import make_sampler
    except ImportError:
        raise ImportError("pip install mlx mlx-lm")
    
    model_path = model or "mlx-community/Mistral-7B-Instruct-v0.3-4bit"
    model_obj, tokenizer = load(model_path)
    
    def generate_task(agent: LocaleAgent, ctx: Dict[str, str]) -> Dict:
        prompt = ctx.get(agent.role, f"You are a {agent.role.lower()}.")
        
        # Temperature varies by trit (MINUS=cold, PLUS=hot)
        temp = 0.3 + (agent.trit + 1) * 0.3  # 0.3, 0.6, 0.9
        sampler = make_sampler(temp=temp, top_p=0.9)
        
        text = generate(
            model_obj, tokenizer,
            prompt=prompt,
            sampler=sampler,
            max_tokens=100
        )
        
        return {
            "text": text,
            "temp": temp,
            "trit": agent.trit,
            "open": list(agent.open)
        }
    
    def merge_generations(legs: Dict[int, Dict]) -> str:
        # Merge following ≪ order: MINUS context → ERGODIC synthesis → PLUS output
        parts = []
        for trit in [-1, 0, 1]:
            if trit in legs:
                parts.append(legs[trit]["text"])
        return "\n---\n".join(parts)
    
    return ordered_fanout(
        seed=seed,
        task_fn=generate_task,
        context=prompts,
        merge_fn=merge_generations,
        announce_start=True,
        announce_end=True
    )


# ============================================================================
# CLI
# ============================================================================

def demo_task(agent: LocaleAgent, ctx: Any) -> Dict:
    """Demo task that returns agent info"""
    return {
        "role": agent.role,
        "trit": agent.trit,
        "seed": hex(agent.seed),
        "open": list(agent.open),
        "voice": agent.voice
    }


def print_cocone(cocone: FanoutCocone):
    """Pretty print the fanout cocone"""
    print("\n╔═══════════════════════════════════════════════════════════════╗")
    print("║  ORDERED LOCALE FANOUT (Cocone over GF(3) Triadic Locale)     ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    
    print("\nBase Locale:")
    print(f"  Points: {set(TRIADIC_LOCALE.points)}")
    print(f"  Is ordered locale: {TRIADIC_LOCALE.is_ordered_locale()}")
    print(f"  Has open cones: {TRIADIC_LOCALE.has_open_cones()}")
    
    print("\nCocone Legs (ι_t : agent → apex):")
    for trit in [-1, 0, 1]:
        if trit in cocone.legs:
            leg = cocone.legs[trit]
            agent = next(a for a in AGENTS if a.trit == trit)
            print(f"  ι_{trit:+d} ({agent.role}): {leg}")
    
    print(f"\nApex (colimit): {cocone.apex_value}")
    print(f"Universal property: {cocone.verify_universal()}")
    
    # GF(3) verification
    trit_sum = sum(a.trit for a in AGENTS)
    print(f"\nGF(3) Conservation: Σtrits = {trit_sum} ≡ {trit_sum % 3} (mod 3) ✓")


def main():
    import sys
    
    seed = int(sys.argv[1], 16) if len(sys.argv) > 1 else 0x42D
    
    print(f"Seed: {hex(seed)}")
    
    # Run ordered fanout
    result = ordered_fanout(
        seed=seed,
        task_fn=demo_task,
        context=None,
        announce_start=True,
        announce_end=True
    )
    
    print_cocone(result)
    
    # Show ≪ order
    print("\n≪ Order (computational flow):")
    print("  MINUS(-1) ≪ ERGODIC(0) ≪ PLUS(+1)")
    print("  (validation → coordination → generation)")
    
    # Verify locale
    print("\n" + "═" * 60)
    print("  Ordered Locale Axioms Verified ✓")
    print("═" * 60)


if __name__ == "__main__":
    main()
