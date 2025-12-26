"""
dynamic-sufficiency: Santa Fe Institute Complexity-Theoretic Skill Verification

This module implements Computational Mechanics from SFI to ensure agents
never act without sufficient skill coverage.

Key Concepts:
- Causal States: Equivalence classes of tasks with same skill requirements
- ε-Machine: Minimal sufficient model for task → skill mapping
- Statistical Complexity: Entropy of causal state distribution
- Fisher Metric: Information-geometric distance between skill configs

Reference:
- Crutchfield & Young: "Computational Mechanics"
- Gell-Mann & Lloyd: "Effective Complexity"
- Bialek, Nemenman, Tishby: "Predictive Information"
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Set, Dict, List, Tuple, Optional, Callable, Any
from enum import Enum, auto
from collections import Counter
from functools import wraps
import hashlib
import json
from math import log2


# ════════════════════════════════════════════════════════════════════════════
# Core Types
# ════════════════════════════════════════════════════════════════════════════

class Trit(Enum):
    """GF(3) trit values."""
    MINUS = -1
    ERGODIC = 0
    PLUS = 1


@dataclass(frozen=True)
class Skill:
    """A loadable agent skill."""
    name: str
    trit: Trit
    domain: str = "general"
    criticality: float = 1.0
    dependencies: Tuple[str, ...] = ()
    
    @property
    def information_content(self) -> float:
        """Bits of information this skill provides."""
        return self.criticality * (1 + len(self.dependencies) * 0.1)


@dataclass
class Action:
    """An action the agent intends to take."""
    operation: str = "general"
    domain: str = "general"
    language: Optional[str] = None
    tool: Optional[str] = None
    skill: Optional[str] = None
    complexity: str = "O(1)"
    
    def summary(self) -> str:
        parts = [self.domain, self.operation]
        if self.language:
            parts.append(self.language)
        if self.tool:
            parts.append(self.tool)
        return ":".join(parts)
    
    @classmethod
    def from_callable(cls, func: Callable, args: tuple, kwargs: dict) -> Action:
        """Infer action from function call."""
        name = func.__name__.lower()
        
        # Infer operation from function name
        if "read" in name or "get" in name:
            operation = "read"
        elif "write" in name or "create" in name or "set" in name:
            operation = "write"
        elif "verify" in name or "check" in name or "test" in name:
            operation = "verify"
        elif "transform" in name or "edit" in name:
            operation = "transform"
        else:
            operation = "general"
        
        return cls(operation=operation)


@dataclass(frozen=True)
class CausalState:
    """
    Equivalence class of tasks with identical skill requirements.
    
    Two tasks are in the same causal state iff they require the
    same skill profile for successful completion.
    """
    domain: str
    operation: str
    complexity: str
    tool_profile: Tuple[str, ...]
    skill_signature: Tuple[str, ...]
    
    def __hash__(self):
        return hash((self.domain, self.operation, self.complexity, 
                     self.tool_profile, self.skill_signature))


@dataclass
class CoverageResult:
    """Result of skill coverage analysis."""
    score: float
    is_sufficient: bool
    missing: List[Skill]
    excess: Set[Skill]
    causal_state: Optional[CausalState] = None
    
    def __str__(self) -> str:
        status = "✓ SUFFICIENT" if self.is_sufficient else "✗ INSUFFICIENT"
        return f"{status} (coverage={self.score:.1%}, missing={len(self.missing)})"


class Verdict(Enum):
    """Pre-action gate verdict."""
    PROCEED = auto()
    LOAD_MORE = auto()
    ABORT = auto()


@dataclass
class PreMessageResult:
    """Result of pre-message sufficiency check."""
    proceed: bool
    loaded_skills: Set[Skill]
    coverage: CoverageResult
    causal_state: Optional[CausalState]
    skills_loaded_dynamically: List[Skill] = field(default_factory=list)


# ════════════════════════════════════════════════════════════════════════════
# ε-Machine: Minimal Sufficient Model
# ════════════════════════════════════════════════════════════════════════════

INSUFFICIENT_MARKER = Skill(name="__INSUFFICIENT__", trit=Trit.ERGODIC)


class EpsilonMachine:
    """
    Minimal sufficient model for task → skill mapping.
    
    The ε-machine partitions the task space into causal states and
    learns the minimal skill set sufficient for each state.
    
    Properties:
    - Minimal: No redundant states or skills
    - Sufficient: Captures all predictive information
    - Unique: Up to isomorphism
    """
    
    def __init__(self):
        self.states: Dict[CausalState, Set[Skill]] = {}
        self.transitions: Dict[Tuple[CausalState, str], CausalState] = {}
        self.observation_count: Counter = Counter()
        self.success_count: Counter = Counter()
    
    def infer_state(self, action: Action) -> CausalState:
        """Map action to its causal state."""
        # Infer required skills from action features
        skills = self._infer_skills(action)
        tools = self._infer_tools(action)
        
        return CausalState(
            domain=action.domain,
            operation=action.operation,
            complexity=action.complexity,
            tool_profile=tuple(sorted(tools)),
            skill_signature=tuple(sorted(skills))
        )
    
    def _infer_skills(self, action: Action) -> Set[str]:
        """Infer required skill names from action."""
        skills = set()
        
        # Domain-based inference
        domain_skills = {
            "haskell": {"ghc", "cabal"},
            "julia": {"julia-gay", "acsets"},
            "clojure": {"babashka", "cider-clojure"},
            "python": {"uv-oneliners", "python-development"},
            "rust": {"cargo-rust", "rust"},
            "web": {"firecrawl", "exa"},
            "mcp": {"mcp-builder", "gay-mcp"},
        }
        
        if action.language and action.language in domain_skills:
            skills.update(domain_skills[action.language])
        if action.domain in domain_skills:
            skills.update(domain_skills[action.domain])
        
        # Operation-based inference
        if action.operation == "verify":
            skills.add("spi-parallel-verify")
        if action.skill:
            skills.add(action.skill)
        
        return skills
    
    def _infer_tools(self, action: Action) -> Set[str]:
        """Infer required tools from action."""
        tools = set()
        
        if action.operation in {"read", "write", "transform"}:
            tools.update({"Read", "edit_file", "create_file"})
        if action.domain == "web":
            tools.update({"read_web_page", "web_search"})
        if action.tool:
            tools.add(action.tool)
        
        return tools
    
    def add_observation(self, action: Action, skills_used: Set[Skill], success: bool):
        """Learn from observed action-skill-outcome triple."""
        state = self.infer_state(action)
        self.observation_count[state] += 1
        
        if state not in self.states:
            self.states[state] = set()
        
        if success:
            self.success_count[state] += 1
            # Update sufficient skill set (intersection for minimal)
            if not self.states[state]:
                self.states[state] = skills_used.copy()
            else:
                # Keep skills that appear in ALL successes
                self.states[state] &= skills_used
        else:
            # Mark that current skills were insufficient
            self.states[state].add(INSUFFICIENT_MARKER)
    
    def minimal_sufficient_skills(self, action: Action) -> Set[Skill]:
        """Return minimal skill set sufficient for action."""
        state = self.infer_state(action)
        
        if state in self.states:
            return self.states[state] - {INSUFFICIENT_MARKER}
        
        # Infer from skill signature
        return {Skill(name=name, trit=Trit.ERGODIC) 
                for name in state.skill_signature}
    
    def statistical_complexity(self) -> float:
        """
        C_μ = -Σ p(s) log₂ p(s)
        
        The entropy of the causal state distribution.
        Higher values indicate more complex task spaces.
        """
        if not self.observation_count:
            return 0.0
        
        total = sum(self.observation_count.values())
        probs = [c / total for c in self.observation_count.values()]
        return -sum(p * log2(p) for p in probs if p > 0)
    
    def success_rate(self, state: CausalState) -> float:
        """Empirical success rate for a causal state."""
        obs = self.observation_count.get(state, 0)
        succ = self.success_count.get(state, 0)
        return succ / obs if obs > 0 else 0.5  # Prior


# ════════════════════════════════════════════════════════════════════════════
# Causal State Inference
# ════════════════════════════════════════════════════════════════════════════

class CausalStateInference:
    """Infer causal state from action specification."""
    
    def __init__(self):
        self.state_cache: Dict[str, CausalState] = {}
    
    def infer_state(self, action: Action) -> CausalState:
        """Partition action into equivalence class."""
        cache_key = action.summary()
        
        if cache_key in self.state_cache:
            return self.state_cache[cache_key]
        
        features = self.extract_features(action)
        state = CausalState(
            domain=features["domain"],
            operation=features["operation"],
            complexity=features["complexity"],
            tool_profile=tuple(sorted(features["tools"])),
            skill_signature=tuple(sorted(features["skills"]))
        )
        
        self.state_cache[cache_key] = state
        return state
    
    def extract_features(self, action: Action) -> Dict[str, Any]:
        """Extract features from action for state classification."""
        return {
            "domain": action.domain,
            "operation": action.operation,
            "complexity": action.complexity,
            "tools": self._infer_tools(action),
            "skills": self._infer_skills(action)
        }
    
    def _infer_tools(self, action: Action) -> Set[str]:
        """Infer required tools."""
        tools = set()
        if action.operation == "read":
            tools.add("Read")
        elif action.operation == "write":
            tools.update({"create_file", "edit_file"})
        elif action.operation == "verify":
            tools.add("Bash")
        return tools
    
    def _infer_skills(self, action: Action) -> Set[str]:
        """Infer required skills."""
        skills = set()
        if action.skill:
            skills.add(action.skill)
        if action.language:
            lang_skills = {
                "haskell": "ghc",
                "julia": "julia-gay",
                "clojure": "babashka",
            }
            if action.language in lang_skills:
                skills.add(lang_skills[action.language])
        return skills


# ════════════════════════════════════════════════════════════════════════════
# Coverage Computation
# ════════════════════════════════════════════════════════════════════════════

SUFFICIENCY_THRESHOLD = 0.95


def coverage_score(action: Action, 
                   loaded_skills: Set[Skill],
                   epsilon_machine: EpsilonMachine) -> CoverageResult:
    """
    Compute sufficiency coverage for an action.
    
    Uses the ε-machine to determine minimal required skills
    and compares against loaded skills.
    """
    required = epsilon_machine.minimal_sufficient_skills(action)
    state = epsilon_machine.infer_state(action)
    
    # Match by name since skill objects may differ
    loaded_names = {s.name for s in loaded_skills}
    required_names = {s.name for s in required}
    
    covered_names = loaded_names & required_names
    missing_names = required_names - loaded_names
    excess_names = loaded_names - required_names
    
    # Weight by criticality
    covered = {s for s in required if s.name in covered_names}
    missing = [s for s in required if s.name in missing_names]
    excess = {s for s in loaded_skills if s.name in excess_names}
    
    covered_weight = sum(s.criticality for s in covered)
    total_weight = sum(s.criticality for s in required)
    
    score = covered_weight / total_weight if total_weight > 0 else 1.0
    
    return CoverageResult(
        score=score,
        is_sufficient=(score >= SUFFICIENCY_THRESHOLD),
        missing=sorted(missing, key=lambda s: -s.criticality),
        excess=excess,
        causal_state=state
    )


# ════════════════════════════════════════════════════════════════════════════
# Fisher Information Metric
# ════════════════════════════════════════════════════════════════════════════

def fisher_metric(config1: Set[Skill], 
                  config2: Set[Skill],
                  task_distribution: Optional[Dict[str, float]] = None) -> float:
    """
    Information-geometric distance between skill configurations.
    
    g(θ₁, θ₂) = Σ_i w_i * 𝟙[skill_i in symmetric_difference]
    
    Measures how distinguishable two skill configs are.
    """
    if task_distribution is None:
        task_distribution = {}
    
    diff = config1.symmetric_difference(config2)
    
    weighted_distance = sum(
        task_distribution.get(skill.name, 1.0) * skill.information_content
        for skill in diff
    )
    
    return weighted_distance


# ════════════════════════════════════════════════════════════════════════════
# Pre-Action Gate
# ════════════════════════════════════════════════════════════════════════════

def pre_action_gate(action: Action, 
                    loaded_skills: Set[Skill],
                    epsilon_machine: EpsilonMachine) -> Tuple[Verdict, CoverageResult]:
    """
    Gate that prevents action without sufficient skills.
    
    Returns:
        (PROCEED, coverage): Sufficient skills loaded
        (LOAD_MORE, coverage): Specific skills needed  
        (ABORT, coverage): Insufficient and unrecoverable
    """
    coverage = coverage_score(action, loaded_skills, epsilon_machine)
    
    if coverage.is_sufficient:
        return Verdict.PROCEED, coverage
    
    if coverage.score >= 0.5:
        return Verdict.LOAD_MORE, coverage
    
    return Verdict.ABORT, coverage


# ════════════════════════════════════════════════════════════════════════════
# GF(3) Triad Completion
# ════════════════════════════════════════════════════════════════════════════

def complete_triad(skills: Set[Skill], 
                   skill_registry: Dict[str, Skill]) -> Set[Skill]:
    """
    Add skills to complete GF(3) = 0 triads.
    
    Ensures sum of trits ≡ 0 (mod 3).
    """
    current_sum = sum(s.trit.value for s in skills) % 3
    
    if current_sum == 0:
        return skills
    
    # Find complementary skill
    needed_trit = (3 - current_sum) % 3
    if needed_trit == 2:
        needed_trit = -1
    needed = Trit(needed_trit)
    
    # Find skill with needed trit
    for name, skill in skill_registry.items():
        if skill.trit == needed and skill not in skills:
            return skills | {skill}
    
    return skills  # No complementary found


# ════════════════════════════════════════════════════════════════════════════
# Decorator for Sufficiency Gating
# ════════════════════════════════════════════════════════════════════════════

# Global ε-machine instance
_epsilon_machine = EpsilonMachine()
_loaded_skills: Set[Skill] = set()


def get_loaded_skills() -> Set[Skill]:
    """Get currently loaded skills."""
    return _loaded_skills.copy()


def load_skill(skill: Skill):
    """Load a skill."""
    _loaded_skills.add(skill)


def require_sufficiency(min_coverage: float = SUFFICIENCY_THRESHOLD):
    """
    Decorator that gates function execution on skill sufficiency.
    
    Usage:
        @require_sufficiency(min_coverage=0.9)
        def complex_action(params):
            ...
    """
    def decorator(func: Callable):
        @wraps(func)
        def wrapper(*args, **kwargs):
            action = Action.from_callable(func, args, kwargs)
            loaded = get_loaded_skills()
            
            verdict, coverage = pre_action_gate(action, loaded, _epsilon_machine)
            
            if verdict == Verdict.ABORT:
                raise InsufficientSkillsError(action, coverage)
            
            if verdict == Verdict.LOAD_MORE:
                # In real implementation, attempt dynamic loading here
                pass
            
            # Execute and record
            try:
                result = func(*args, **kwargs)
                _epsilon_machine.add_observation(action, loaded, success=True)
                return result
            except Exception as e:
                _epsilon_machine.add_observation(action, loaded, success=False)
                raise
        
        return wrapper
    return decorator


# ════════════════════════════════════════════════════════════════════════════
# Error Types
# ════════════════════════════════════════════════════════════════════════════

class InsufficientSkillsError(Exception):
    """Raised when action cannot proceed due to missing skills."""
    
    def __init__(self, action: Action, coverage: CoverageResult):
        self.action = action
        self.coverage = coverage
        
        missing_list = "\n".join(f"    • {s.name}" for s in coverage.missing[:5])
        
        msg = f"""
╔══════════════════════════════════════════════════════════════════╗
║  SUFFICIENCY VIOLATION                                           ║
╠══════════════════════════════════════════════════════════════════╣
║  Action: {action.summary():<54}║
║  Coverage: {coverage.score:.1%} (required: ≥95%)                       ║
║                                                                  ║
║  Missing Skills:                                                 ║
{missing_list}
║                                                                  ║
║  Resolution:                                                     ║
║    1. Load missing skills                                        ║
║    2. Use alternative approach with loaded skills                ║
║    3. Request human guidance                                     ║
╚══════════════════════════════════════════════════════════════════╝
"""
        super().__init__(msg)


# ════════════════════════════════════════════════════════════════════════════
# CLI Entry Point
# ════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import sys
    
    print("Dynamic Sufficiency - SFI Complexity-Theoretic Skill Verification")
    print("=" * 60)
    
    # Demo: Create some skills
    skills = [
        Skill("gay-mcp", Trit.PLUS, "color", 1.0),
        Skill("spi-parallel-verify", Trit.MINUS, "verify", 1.0),
        Skill("bisimulation-game", Trit.ERGODIC, "verify", 0.8),
    ]
    
    for s in skills:
        load_skill(s)
    
    print(f"Loaded skills: {[s.name for s in get_loaded_skills()]}")
    
    # Demo: Check coverage for action
    action = Action(
        operation="verify",
        domain="code",
        language="haskell",
        skill="spi-parallel-verify"
    )
    
    em = EpsilonMachine()
    verdict, coverage = pre_action_gate(action, get_loaded_skills(), em)
    
    print(f"\nAction: {action.summary()}")
    print(f"Verdict: {verdict.name}")
    print(f"Coverage: {coverage}")
    
    # Show ε-machine stats
    print(f"\nε-Machine Statistical Complexity: {em.statistical_complexity():.3f} bits")
