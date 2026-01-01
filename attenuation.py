#!/usr/bin/env python3
"""
Capability Attenuation for Skill System

Attenuation = reducing authority when passing capabilities.
In our skill system:
- Full capability: all skill operations
- Attenuated: read-only, limited palette, no advance

GF(3) Attenuation Model:
  PLUS (+1)  → ERGODIC (0)  → MINUS (-1)
  [generate] → [transport]  → [validate]
  
Attenuation always flows toward MINUS (restriction).
Amplification (forbidden) would flow toward PLUS.

CapTP Principle: You can only invoke what you've been given.
"""

from dataclasses import dataclass, field
from typing import Set, Dict, List, Optional, Callable, Any, FrozenSet
from enum import IntEnum, Enum, auto
import hashlib
import sys

sys.path.insert(0, '/Users/bob/.claude/skills/dynamic-sufficiency')
from world_memory import Skill, Trit, SKILL_REGISTRY, SkillMemory

# ════════════════════════════════════════════════════════════════════════════
# Attenuation Types
# ════════════════════════════════════════════════════════════════════════════

class AttenuationLevel(IntEnum):
    """Attenuation levels map to trit values (inverted for restriction)."""
    FULL = 1       # Full authority (PLUS equivalent)
    TRANSPORT = 0  # Pass-through only (ERGODIC)
    READONLY = -1  # Read-only access (MINUS)


@dataclass(frozen=True)
class Capability:
    """
    An unforgeable reference to a skill operation.
    
    Capabilities can be:
    1. Attenuated (reduced authority)
    2. Never amplified (no gaining authority)
    3. Introduced (shared with others who can then use)
    """
    skill_name: str
    operations: FrozenSet[str]
    level: AttenuationLevel
    max_invocations: Optional[int] = None  # None = unlimited
    seed_constraint: Optional[int] = None  # Locked to specific seed
    
    def can_invoke(self, operation: str) -> bool:
        """Check if this capability allows the operation."""
        return operation in self.operations
    
    def attenuate(self, 
                  remove_ops: Optional[Set[str]] = None,
                  new_level: Optional[AttenuationLevel] = None,
                  limit_invocations: Optional[int] = None) -> 'Capability':
        """
        Create attenuated (reduced) capability.
        
        INVARIANT: Can only reduce, never amplify.
        """
        # Filter operations (can only remove, not add)
        new_ops = self.operations
        if remove_ops:
            new_ops = self.operations - frozenset(remove_ops)
        
        # Level can only decrease (toward READONLY)
        final_level = self.level
        if new_level is not None:
            if new_level > self.level:
                raise AttenuationViolation(
                    f"Cannot amplify from {self.level.name} to {new_level.name}"
                )
            final_level = new_level
        
        # Invocation limit can only decrease
        final_limit = self.max_invocations
        if limit_invocations is not None:
            if self.max_invocations is None:
                final_limit = limit_invocations
            else:
                final_limit = min(self.max_invocations, limit_invocations)
        
        return Capability(
            skill_name=self.skill_name,
            operations=new_ops,
            level=final_level,
            max_invocations=final_limit,
            seed_constraint=self.seed_constraint
        )
    
    @property
    def trit(self) -> Trit:
        """Map attenuation level to GF(3) trit."""
        return Trit(self.level.value)


class AttenuationViolation(Exception):
    """Raised when attempting to amplify a capability."""
    pass


# ════════════════════════════════════════════════════════════════════════════
# Skill Capability Registry
# ════════════════════════════════════════════════════════════════════════════

# Standard operations for skill categories
SKILL_OPERATIONS = {
    "color": frozenset(["next_color", "color_at", "palette", "advance", "reset"]),
    "verify": frozenset(["check", "validate", "verify", "lint", "test"]),
    "generate": frozenset(["create", "build", "generate", "spawn", "derive"]),
    "transport": frozenset(["route", "dispatch", "send", "receive", "bridge"]),
    "read": frozenset(["read", "get", "list", "search", "query"]),
    "write": frozenset(["write", "set", "update", "delete", "modify"]),
}


def full_capability(skill: Skill) -> Capability:
    """Create full capability for a skill."""
    # Determine operations based on skill trit
    if skill.trit == Trit.PLUS:
        ops = SKILL_OPERATIONS["generate"] | SKILL_OPERATIONS["write"]
    elif skill.trit == Trit.MINUS:
        ops = SKILL_OPERATIONS["verify"] | SKILL_OPERATIONS["read"]
    else:  # ERGODIC
        ops = SKILL_OPERATIONS["transport"] | SKILL_OPERATIONS["read"]
    
    return Capability(
        skill_name=skill.name,
        operations=ops,
        level=AttenuationLevel.FULL,
    )


def readonly_capability(skill: Skill) -> Capability:
    """Create read-only attenuated capability."""
    return Capability(
        skill_name=skill.name,
        operations=SKILL_OPERATIONS["read"],
        level=AttenuationLevel.READONLY,
    )


# ════════════════════════════════════════════════════════════════════════════
# Vat: Capability Container with Transactional Boundary
# ════════════════════════════════════════════════════════════════════════════

@dataclass
class Vat:
    """
    Transactional capability container (from Goblins).
    
    Vats provide:
    1. Isolation: capabilities don't escape without explicit grant
    2. Transaction: all-or-nothing state changes
    3. Attenuation: capabilities can be reduced when shared
    """
    seed: int
    capabilities: Dict[str, Capability] = field(default_factory=dict)
    invocation_counts: Dict[str, int] = field(default_factory=dict)
    
    def spawn(self, skill_name: str, level: AttenuationLevel = AttenuationLevel.FULL) -> Capability:
        """Spawn a capability for a skill in this vat."""
        if skill_name not in SKILL_REGISTRY:
            raise ValueError(f"Unknown skill: {skill_name}")
        
        skill = SKILL_REGISTRY[skill_name]
        cap = full_capability(skill)
        
        # Apply initial attenuation
        if level != AttenuationLevel.FULL:
            cap = cap.attenuate(new_level=level)
        
        # Lock to this vat's seed
        cap = Capability(
            skill_name=cap.skill_name,
            operations=cap.operations,
            level=cap.level,
            max_invocations=cap.max_invocations,
            seed_constraint=self.seed
        )
        
        self.capabilities[skill_name] = cap
        self.invocation_counts[skill_name] = 0
        return cap
    
    def invoke(self, cap: Capability, operation: str) -> bool:
        """
        Invoke an operation on a capability.
        
        Returns True if invocation succeeded, False if denied.
        """
        # Check capability is known to this vat
        if cap.skill_name not in self.capabilities:
            return False
        
        # Check seed constraint
        if cap.seed_constraint is not None and cap.seed_constraint != self.seed:
            return False
        
        # Check operation allowed
        if not cap.can_invoke(operation):
            return False
        
        # Check invocation limit
        if cap.max_invocations is not None:
            count = self.invocation_counts.get(cap.skill_name, 0)
            if count >= cap.max_invocations:
                return False
        
        # Record invocation
        self.invocation_counts[cap.skill_name] = self.invocation_counts.get(cap.skill_name, 0) + 1
        return True
    
    def grant(self, skill_name: str, 
              to_vat: 'Vat',
              attenuate_ops: Optional[Set[str]] = None,
              attenuate_level: Optional[AttenuationLevel] = None,
              limit: Optional[int] = None) -> Optional[Capability]:
        """
        Grant a capability to another vat with optional attenuation.
        
        POLA: Grant only what's needed, nothing more.
        """
        if skill_name not in self.capabilities:
            return None
        
        cap = self.capabilities[skill_name]
        
        # Attenuate before granting
        attenuated = cap.attenuate(
            remove_ops=attenuate_ops,
            new_level=attenuate_level,
            limit_invocations=limit
        )
        
        # Register in target vat (with new seed constraint)
        to_vat.capabilities[skill_name] = Capability(
            skill_name=attenuated.skill_name,
            operations=attenuated.operations,
            level=attenuated.level,
            max_invocations=attenuated.max_invocations,
            seed_constraint=to_vat.seed  # Re-bind to target seed
        )
        
        return to_vat.capabilities[skill_name]
    
    def gf3_sum(self) -> int:
        """Compute GF(3) sum of all capabilities."""
        return sum(cap.trit.value for cap in self.capabilities.values()) % 3


# ════════════════════════════════════════════════════════════════════════════
# Attenuation Chains for Skill Delegation
# ════════════════════════════════════════════════════════════════════════════

@dataclass
class AttenuationChain:
    """
    Track attenuation through delegation chain.
    
    Each delegation can only reduce, creating a monotonic
    decrease in authority.
    """
    original: Capability
    chain: List[Capability] = field(default_factory=list)
    
    def delegate(self, 
                 remove_ops: Optional[Set[str]] = None,
                 new_level: Optional[AttenuationLevel] = None,
                 limit: Optional[int] = None) -> Capability:
        """Add delegation step to chain."""
        current = self.chain[-1] if self.chain else self.original
        attenuated = current.attenuate(remove_ops, new_level, limit)
        self.chain.append(attenuated)
        return attenuated
    
    @property
    def current(self) -> Capability:
        """Get current (most attenuated) capability."""
        return self.chain[-1] if self.chain else self.original
    
    @property
    def attenuation_depth(self) -> int:
        """How many attenuation steps from original."""
        return len(self.chain)
    
    def verify_monotonic(self) -> bool:
        """Verify chain is monotonically decreasing in authority."""
        prev = self.original
        for cap in self.chain:
            # Level should not increase
            if cap.level > prev.level:
                return False
            # Operations should not expand
            if not cap.operations.issubset(prev.operations):
                return False
            # Invocation limit should not increase
            if prev.max_invocations is not None:
                if cap.max_invocations is None or cap.max_invocations > prev.max_invocations:
                    return False
            prev = cap
        return True


# ════════════════════════════════════════════════════════════════════════════
# Integration with Dynamic Sufficiency
# ════════════════════════════════════════════════════════════════════════════

def attenuated_coverage(caps: Set[Capability], required_ops: Set[str]) -> float:
    """
    Compute coverage score accounting for attenuation.
    
    More attenuated capabilities provide less coverage.
    """
    if not required_ops:
        return 1.0
    
    covered = set()
    for cap in caps:
        for op in required_ops:
            if cap.can_invoke(op):
                # Weight by attenuation level
                weight = (cap.level.value + 2) / 3  # Maps -1,0,1 to 1/3, 2/3, 1
                if weight >= 0.5:  # Only count if sufficient authority
                    covered.add(op)
    
    return len(covered) / len(required_ops)


# ════════════════════════════════════════════════════════════════════════════
# Demo
# ════════════════════════════════════════════════════════════════════════════

def demo():
    print("=" * 70)
    print("CAPABILITY ATTENUATION DEMO")
    print("=" * 70)
    
    # Create vats
    alice_vat = Vat(seed=0x42D)
    bob_vat = Vat(seed=0x1069)
    
    print("\n─── Vat Creation ───")
    print(f"  Alice vat (seed=0x42D)")
    print(f"  Bob vat (seed=0x1069)")
    
    # Alice spawns capabilities
    print("\n─── Alice Spawns Capabilities ───")
    gay_mcp = alice_vat.spawn("gay-mcp")
    print(f"  gay-mcp: {gay_mcp.operations}")
    print(f"    Level: {gay_mcp.level.name}, Trit: {gay_mcp.trit.name}")
    
    spi = alice_vat.spawn("spi-parallel-verify")
    print(f"  spi-parallel-verify: {spi.operations}")
    print(f"    Level: {spi.level.name}, Trit: {spi.trit.name}")
    
    dispatch = alice_vat.spawn("skill-dispatch")
    print(f"  skill-dispatch: {dispatch.operations}")
    print(f"    Level: {dispatch.level.name}, Trit: {dispatch.trit.name}")
    
    print(f"\n  Alice GF(3) sum: {alice_vat.gf3_sum()} (should be 0)")
    
    # Alice grants attenuated capability to Bob
    print("\n─── Attenuation: Alice → Bob ───")
    
    # Full capability for color generation
    bob_color = alice_vat.grant(
        "gay-mcp", bob_vat,
        attenuate_ops={"reset", "advance"},  # Remove these
        attenuate_level=AttenuationLevel.TRANSPORT,
        limit=100
    )
    print(f"  Granted gay-mcp to Bob:")
    print(f"    Operations: {bob_color.operations}")
    print(f"    Level: {bob_color.level.name} (was FULL)")
    print(f"    Limit: {bob_color.max_invocations} invocations")
    
    # Read-only for verification
    bob_verify = alice_vat.grant(
        "spi-parallel-verify", bob_vat,
        attenuate_level=AttenuationLevel.READONLY,
        limit=10
    )
    print(f"  Granted spi-parallel-verify to Bob:")
    print(f"    Operations: {bob_verify.operations}")
    print(f"    Level: {bob_verify.level.name}")
    print(f"    Limit: {bob_verify.max_invocations} invocations")
    
    # Attempt amplification (should fail)
    print("\n─── Amplification Attempt (Should Fail) ───")
    try:
        bob_color.attenuate(new_level=AttenuationLevel.FULL)
        print("  ERROR: Amplification succeeded (should not happen)")
    except AttenuationViolation as e:
        print(f"  ✓ Blocked: {e}")
    
    # Attenuation chain
    print("\n─── Attenuation Chain Demo ───")
    chain = AttenuationChain(gay_mcp)
    
    step1 = chain.delegate(new_level=AttenuationLevel.TRANSPORT)
    print(f"  Step 1: FULL → TRANSPORT")
    print(f"    Operations: {len(step1.operations)}")
    
    step2 = chain.delegate(remove_ops={"create", "spawn"}, limit=50)
    print(f"  Step 2: Remove create/spawn, limit 50")
    print(f"    Operations: {len(step2.operations)}")
    
    step3 = chain.delegate(new_level=AttenuationLevel.READONLY)
    print(f"  Step 3: → READONLY")
    print(f"    Operations: {step3.operations}")
    
    print(f"\n  Chain depth: {chain.attenuation_depth}")
    print(f"  Monotonic: {'✓' if chain.verify_monotonic() else '✗'}")
    
    # Coverage with attenuation
    print("\n─── Attenuated Coverage ───")
    required_ops = {"read", "generate", "verify", "create"}
    
    full_caps = {gay_mcp, spi}
    attenuated_caps = {bob_color, bob_verify}
    
    full_cov = attenuated_coverage(full_caps, required_ops)
    attn_cov = attenuated_coverage(attenuated_caps, required_ops)
    
    print(f"  Required ops: {required_ops}")
    print(f"  Full capabilities coverage: {full_cov:.1%}")
    print(f"  Attenuated coverage: {attn_cov:.1%}")
    print(f"  Authority reduction: {(1 - attn_cov/full_cov)*100:.0f}%")
    
    # Invocation test
    print("\n─── Invocation Tests ───")
    
    tests = [
        (bob_color, "palette", "Should succeed"),
        (bob_color, "reset", "Should fail (removed)"),
        (bob_verify, "verify", "Should succeed"),
        (bob_verify, "create", "Should fail (readonly)"),
    ]
    
    for cap, op, expected in tests:
        result = bob_vat.invoke(cap, op)
        status = "✓" if result else "✗"
        print(f"  {status} {cap.skill_name}.{op}: {expected}")

if __name__ == "__main__":
    demo()
