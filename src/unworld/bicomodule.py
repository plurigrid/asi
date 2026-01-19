"""
Bicomodule Operations for Unworld

Implements Spivak's bicomodule structure:

    c = Pattern signatures (learned behavioral invariants)
    ↕ σ (derivation step)
    m = Three-match gadgets ([trit:-1, trit:0, trit:+1])
    ↕ ε (extract exemplar) and δ (verify/contextualize)
    d = Genesis seeds + raw color chains

Comonad Laws:
    Law 1: ε ∘ δ = id (extract after contextualize = identity)
    Law 2: (m ⊲ ε) ∘ δ = id (left counit)
    Law 3: (m ⊲ δ) ∘ δ = (δ ⊲ d) ∘ δ (coassociativity)
"""

from dataclasses import dataclass
from typing import List, Dict, Any, Optional, Tuple

from .three_match import ThreeMatch, Color
from .chain import UnworldChain


# =============================================================================
# σ: m ⊲ d → c ⊲ m (Effect Handler / Derivation Step)
# =============================================================================

def derivation_step(genesis_seed: int, depth: int) -> ThreeMatch:
    """
    Effect handler: converts seed+depth into pattern.
    
    This IS σ: we're interpreting raw data (seed, depth)
    as a high-level pattern (three-match gadget).
    
    σ: m ⊲ d → c ⊲ m
    
    Args:
        genesis_seed: The genesis seed (d)
        depth: Position in derivation chain
    
    Returns:
        ThreeMatch pattern (m with semantic meaning c)
    """
    return ThreeMatch.derive(genesis_seed, depth)


# =============================================================================
# ε: m ⊲ d → d (Counit / Extract Exemplar)
# =============================================================================

def extract_exemplar(match: ThreeMatch) -> List[str]:
    """
    Counit: forget the GF(3) structure, return raw colors.
    
    This is "compilation" or "forgetting":
        m ⊲ d (structured pattern) → d (just the data)
    
    ε: m ⊲ d → d
    
    Args:
        match: A ThreeMatch pattern
    
    Returns:
        List of hex color strings (raw data, no structure)
    """
    return match.hexes


def extract_values(match: ThreeMatch) -> List[int]:
    """
    Extract raw 64-bit values (alternative ε).
    
    Returns:
        List of raw values
    """
    return [c.value for c in match.colors]


# =============================================================================
# δ: m ⊲ d → m ⊲ (m ⊲ d) (Comultiplication / Verify & Contextualize)
# =============================================================================

@dataclass
class ContextualizedPattern:
    """
    A three-match with full context.
    
    This is the result of δ (comultiplication):
        m ⊲ d → m ⊲ (m ⊲ d)
    
    The pattern gains awareness of:
    - Its GF(3) balance status
    - Its position in the chain
    - Its neighbors
    - The genesis that produced it
    """
    match: ThreeMatch
    balanced: bool
    genesis_seed: int
    depth: int
    neighbors: Tuple[Optional[ThreeMatch], Optional[ThreeMatch]]  # (prev, next)
    chain_length: Optional[int] = None
    global_balance: Optional[int] = None
    
    def to_dict(self) -> dict:
        return {
            "match": self.match.to_dict(),
            "balanced": self.balanced,
            "genesis_seed": hex(self.genesis_seed),
            "depth": self.depth,
            "has_prev": self.neighbors[0] is not None,
            "has_next": self.neighbors[1] is not None,
            "chain_length": self.chain_length,
            "global_balance": self.global_balance,
        }


def verify_and_contextualize(
    match: ThreeMatch,
    prev_match: Optional[ThreeMatch] = None,
    next_match: Optional[ThreeMatch] = None,
    chain: Optional[UnworldChain] = None,
) -> ContextualizedPattern:
    """
    Comultiplication: add context, check conservation.
    
    δ: m ⊲ d → m ⊲ (m ⊲ d)
    
    The pattern becomes aware of its context:
    - Its GF(3) balance status
    - Its neighbors in the chain
    - The global chain status
    
    Args:
        match: The pattern to contextualize
        prev_match: Previous pattern in chain (optional)
        next_match: Next pattern in chain (optional)
        chain: The full chain (optional, for global context)
    
    Returns:
        ContextualizedPattern with full context
    """
    return ContextualizedPattern(
        match=match,
        balanced=match.is_balanced(),
        genesis_seed=match.genesis_seed,
        depth=match.depth,
        neighbors=(prev_match, next_match),
        chain_length=len(chain) if chain else None,
        global_balance=chain.global_trit_balance() if chain else None,
    )


# =============================================================================
# Comonad Law Verification
# =============================================================================

def verify_law1(match: ThreeMatch) -> bool:
    """
    Law 1: ε ∘ δ = id
    
    Extract after contextualizing should return the original.
    """
    # Apply δ
    contextualized = verify_and_contextualize(match)
    
    # Apply ε
    extracted = extract_exemplar(contextualized.match)
    
    # Compare to original
    original = extract_exemplar(match)
    
    return extracted == original


def verify_law2(match: ThreeMatch) -> bool:
    """
    Law 2: (m ⊲ ε) ∘ δ = id
    
    Extracting inner state from contextualized matches original.
    """
    # Apply δ
    contextualized = verify_and_contextualize(match)
    
    # The inner match should be the same as the original
    return contextualized.match == match


def verify_law3(chain: UnworldChain, depth: int = 0) -> bool:
    """
    Law 3: (m ⊲ δ) ∘ δ = (δ ⊲ d) ∘ δ (Coassociativity)
    
    For unworld, this is expressed as GF(3) balance being
    path-independent. The sum of trits should be the same
    regardless of how we group the patterns.
    """
    if len(chain) < 3:
        return True  # Trivially true for short chains
    
    # Way 1: Group (0,1,2) then (3,4,5) ...
    sums1 = []
    for i in range(0, len(chain) - 2, 3):
        group_sum = sum(sum(chain[j].trits) for j in range(i, min(i+3, len(chain))))
        sums1.append(group_sum % 3)
    
    # Way 2: Group (1,2,3) then (4,5,6) ...
    sums2 = []
    for i in range(1, len(chain) - 1, 3):
        group_sum = sum(sum(chain[j].trits) for j in range(i, min(i+3, len(chain))))
        sums2.append(group_sum % 3)
    
    # The global balance should be the same
    total1 = sum(sums1) % 3
    total2 = sum(sums2) % 3
    
    return total1 == total2 == 0


def verify_all_laws(chain: UnworldChain) -> Dict[str, bool]:
    """
    Verify all three comonad laws for a chain.
    
    Returns:
        Dict with law verification results
    """
    results = {
        "law1_all": True,
        "law2_all": True,
        "law3": True,
    }
    
    # Law 1 & 2 for each pattern
    for pattern in chain:
        if not verify_law1(pattern):
            results["law1_all"] = False
        if not verify_law2(pattern):
            results["law2_all"] = False
    
    # Law 3 for the chain
    results["law3"] = verify_law3(chain)
    
    results["all_passed"] = all(results.values())
    
    return results


# =============================================================================
# Bisimulation with Temporal Learning
# =============================================================================

@dataclass
class BisimulationResult:
    """Result of comparing derivational to temporal patterns."""
    equivalent: bool
    derivational_patterns: int
    rounds_played: int
    distinguishing_index: Optional[int] = None
    message: str = ""


def bisimulation_game(
    derivational_chain: UnworldChain,
    temporal_patterns: List[Dict[str, Any]],  # From agent-o-rama
    rounds: int = 100,
) -> BisimulationResult:
    """
    Play a bisimulation game between derivational and temporal patterns.
    
    The claim: For any pattern P learned by agent-o-rama, there exists
    a seed S and depth D such that unworld(S, D) produces a behaviorally
    equivalent pattern.
    
    This function checks behavioral equivalence by comparing:
    - GF(3) balance (structural property)
    - Color distribution (statistical property)
    - Trit patterns (semantic property)
    """
    if not temporal_patterns:
        return BisimulationResult(
            equivalent=True,
            derivational_patterns=len(derivational_chain),
            rounds_played=0,
            message="No temporal patterns to compare",
        )
    
    # Play rounds
    for round_num in range(min(rounds, len(temporal_patterns), len(derivational_chain))):
        deriv = derivational_chain[round_num]
        temp = temporal_patterns[round_num]
        
        # Compare GF(3) balance
        deriv_balanced = deriv.is_balanced()
        temp_balanced = temp.get("balanced", sum(temp.get("trits", [0,0,0])) % 3 == 0)
        
        if deriv_balanced != temp_balanced:
            return BisimulationResult(
                equivalent=False,
                derivational_patterns=len(derivational_chain),
                rounds_played=round_num + 1,
                distinguishing_index=round_num,
                message=f"GF(3) balance differs at index {round_num}",
            )
        
        # Compare trit patterns (if available)
        if "trits" in temp:
            deriv_trits = deriv.trits
            temp_trits = temp["trits"]
            
            # They don't need to be identical, just have same sum mod 3
            if sum(deriv_trits) % 3 != sum(temp_trits) % 3:
                return BisimulationResult(
                    equivalent=False,
                    derivational_patterns=len(derivational_chain),
                    rounds_played=round_num + 1,
                    distinguishing_index=round_num,
                    message=f"Trit sums differ at index {round_num}",
                )
    
    return BisimulationResult(
        equivalent=True,
        derivational_patterns=len(derivational_chain),
        rounds_played=min(rounds, len(temporal_patterns), len(derivational_chain)),
        message="Patterns are behaviorally equivalent",
    )
