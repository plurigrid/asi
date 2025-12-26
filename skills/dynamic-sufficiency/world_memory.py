"""
world_memory.py - Skills as World-Generating Self-Improvising Memories

Based on the insight that skills are not static knowledge but:
1. WORLD-GENERATING: Each skill generates a local world model for its domain
2. SELF-IMPROVISING: Skills learn from observations via ε-machine updates
3. MEMORIES: Skills are crystallized patterns of successful action

This module implements the memory substrate that connects:
- dynamic-sufficiency (-1): Validates sufficiency before action
- skill-dispatch (0): Routes tasks to appropriate skill triads
- skill-installer (+1): Generates/loads new skill capabilities

Together they form a closed autopoietic loop where the agent:
1. Observes task → infers causal state
2. Checks sufficiency → loads missing skills
3. Executes → records outcome
4. Improves → updates world model

SFI Foundations:
- Causal states partition task space into equivalence classes
- ε-machine is the minimal sufficient model
- Skills are generative models that sample action policies
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Set, Dict, List, Tuple, Optional, Callable, Any, Iterator
from enum import Enum, IntEnum
from collections import Counter, defaultdict
from functools import lru_cache
import hashlib
import json
import re
from math import log2, exp


# ════════════════════════════════════════════════════════════════════════════
# GF(3) Triadic Types
# ════════════════════════════════════════════════════════════════════════════

class Trit(IntEnum):
    MINUS = -1    # Validator/Verifier
    ERGODIC = 0   # Coordinator/Router
    PLUS = 1      # Generator/Creator


TRIT_ROLES = {
    Trit.MINUS: {
        "name": "validator",
        "color": "#2626D8",
        "verbs": ["verify", "constrain", "reduce", "filter", "lint", "check", "validate"],
    },
    Trit.ERGODIC: {
        "name": "coordinator",
        "color": "#26D826", 
        "verbs": ["transport", "derive", "navigate", "bridge", "arrange", "dispatch", "route"],
    },
    Trit.PLUS: {
        "name": "generator",
        "color": "#D82626",
        "verbs": ["create", "compose", "generate", "expand", "train", "build", "install"],
    },
}


# ════════════════════════════════════════════════════════════════════════════
# Skill as World-Generating Memory
# ════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Skill:
    """
    A skill as a world-generating, self-improvising memory.
    
    Each skill is a crystallized world-model that:
    - Generates appropriate action policies for its domain
    - Improves through observation of outcomes
    - Participates in GF(3) triadic compositions
    """
    name: str
    trit: Trit
    bundle: str = "general"
    domain: str = "general"
    criticality: float = 1.0
    dependencies: Tuple[str, ...] = ()
    keywords: Tuple[str, ...] = ()
    action_verbs: Tuple[str, ...] = ()
    
    @property
    def information_content(self) -> float:
        """Bits of information this skill provides."""
        base = self.criticality
        dep_bonus = len(self.dependencies) * 0.1
        keyword_bonus = len(self.keywords) * 0.05
        return base + dep_bonus + keyword_bonus
    
    @property
    def role(self) -> str:
        return TRIT_ROLES[self.trit]["name"]
    
    @property 
    def color(self) -> str:
        return TRIT_ROLES[self.trit]["color"]
    
    def matches_action(self, action_verb: str) -> bool:
        """Check if this skill matches an action verb."""
        action_lower = action_verb.lower()
        return (
            action_lower in self.action_verbs or
            action_lower in TRIT_ROLES[self.trit]["verbs"]
        )
    
    def matches_keywords(self, text: str) -> float:
        """Compute keyword match score for text."""
        text_lower = text.lower()
        matches = sum(1 for kw in self.keywords if kw.lower() in text_lower)
        return matches / len(self.keywords) if self.keywords else 0.0


# ════════════════════════════════════════════════════════════════════════════
# Comprehensive Skill Registry
# ════════════════════════════════════════════════════════════════════════════

SKILL_REGISTRY: Dict[str, Skill] = {
    # ─── MINUS (-1): Validators ───
    "dynamic-sufficiency": Skill(
        "dynamic-sufficiency", Trit.MINUS, "core", "verification",
        criticality=1.0,
        keywords=("sufficiency", "coverage", "epsilon-machine", "causal-state"),
        action_verbs=("gate", "verify", "check"),
    ),
    "sheaf-cohomology": Skill(
        "sheaf-cohomology", Trit.MINUS, "cohomological", "math",
        criticality=0.9,
        keywords=("cech", "cohomology", "sheaf", "local-global"),
        action_verbs=("verify", "check"),
    ),
    "three-match": Skill(
        "three-match", Trit.MINUS, "core", "sat",
        criticality=0.8,
        keywords=("3sat", "gadget", "isomorphism", "subgraph"),
        action_verbs=("reduce", "match"),
    ),
    "clj-kondo-3color": Skill(
        "clj-kondo-3color", Trit.MINUS, "database", "clojure",
        criticality=0.9,
        keywords=("lint", "kondo", "clojure", "analyze"),
        action_verbs=("lint", "analyze"),
        dependencies=("babashka",),
    ),
    "spi-parallel-verify": Skill(
        "spi-parallel-verify", Trit.MINUS, "verification", "parallel",
        criticality=1.0,
        keywords=("spi", "parallel", "verify", "invariance"),
        action_verbs=("verify", "check"),
    ),
    "persistent-homology": Skill(
        "persistent-homology", Trit.MINUS, "topology", "math",
        criticality=0.8,
        keywords=("homology", "topology", "persistent", "betti"),
        action_verbs=("analyze", "verify"),
    ),
    "dialectica": Skill(
        "dialectica", Trit.MINUS, "logic", "proof",
        criticality=0.7,
        keywords=("dialectica", "godel", "interpretation"),
        action_verbs=("interpret", "verify"),
    ),
    "temporal-coalgebra": Skill(
        "temporal-coalgebra", Trit.MINUS, "math", "stream",
        criticality=0.8,
        keywords=("coalgebra", "bisimulation", "stream", "temporal"),
        action_verbs=("observe", "verify"),
    ),
    "opam-ocaml": Skill(
        "opam-ocaml", Trit.MINUS, "ocaml", "package",
        criticality=0.8,
        keywords=("opam", "ocaml", "switch", "package"),
        action_verbs=("install", "switch"),
    ),
    "intent-sink": Skill(
        "intent-sink", Trit.MINUS, "resource", "gc",
        criticality=0.7,
        keywords=("intent", "nullify", "sink", "gc"),
        action_verbs=("nullify", "absorb"),
    ),
    "soliton-detection": Skill(
        "soliton-detection", Trit.MINUS, "topology", "agency",
        criticality=0.7,
        keywords=("soliton", "defect", "topological", "anyon"),
        action_verbs=("detect", "analyze"),
    ),
    "webapp-testing": Skill(
        "webapp-testing", Trit.MINUS, "testing", "web",
        criticality=0.9,
        keywords=("playwright", "test", "browser", "selenium"),
        action_verbs=("test", "verify"),
    ),
    
    # ─── ERGODIC (0): Coordinators ───
    "skill-dispatch": Skill(
        "skill-dispatch", Trit.ERGODIC, "core", "routing",
        criticality=1.0,
        keywords=("dispatch", "route", "triad", "bundle"),
        action_verbs=("dispatch", "route", "assign"),
    ),
    "unworld": Skill(
        "unworld", Trit.ERGODIC, "core", "derivation",
        criticality=1.0,
        keywords=("derive", "chain", "seed", "unworld"),
        action_verbs=("derive", "chain"),
    ),
    "acsets": Skill(
        "acsets", Trit.ERGODIC, "database", "category",
        criticality=1.0,
        keywords=("acset", "c-set", "relational", "categorical"),
        action_verbs=("query", "model"),
    ),
    "cognitive-surrogate": Skill(
        "cognitive-surrogate", Trit.ERGODIC, "learning", "psychology",
        criticality=0.9,
        keywords=("surrogate", "cognitive", "predict", "model"),
        action_verbs=("predict", "model"),
    ),
    "entropy-sequencer": Skill(
        "entropy-sequencer", Trit.ERGODIC, "core", "scheduling",
        criticality=0.8,
        keywords=("entropy", "sequence", "interleave", "schedule"),
        action_verbs=("sequence", "arrange"),
    ),
    "babashka": Skill(
        "babashka", Trit.ERGODIC, "clojure", "scripting",
        criticality=1.0,
        keywords=("bb", "babashka", "clojure", "script"),
        action_verbs=("run", "script"),
    ),
    "bisimulation-game": Skill(
        "bisimulation-game", Trit.ERGODIC, "verification", "game",
        criticality=0.8,
        keywords=("bisimulation", "game", "equivalence"),
        action_verbs=("compare", "match"),
    ),
    "self-evolving-agent": Skill(
        "self-evolving-agent", Trit.ERGODIC, "evolution", "agent",
        criticality=1.0,
        keywords=("darwin", "godel", "evolve", "self-improve"),
        action_verbs=("evolve", "mutate"),
    ),
    "duckdb-temporal-versioning": Skill(
        "duckdb-temporal-versioning", Trit.ERGODIC, "database", "temporal",
        criticality=0.9,
        keywords=("duckdb", "temporal", "versioning", "time-travel"),
        action_verbs=("query", "version"),
    ),
    "causal-inference": Skill(
        "causal-inference", Trit.ERGODIC, "learning", "causality",
        criticality=0.9,
        keywords=("causal", "intervention", "counterfactual"),
        action_verbs=("infer", "intervene"),
    ),
    "discopy": Skill(
        "discopy", Trit.ERGODIC, "diagram", "category",
        criticality=0.8,
        keywords=("discopy", "diagram", "monoidal", "string"),
        action_verbs=("compose", "diagram"),
    ),
    "protocol-evolution-markets": Skill(
        "protocol-evolution-markets", Trit.ERGODIC, "markets", "protocol",
        criticality=0.7,
        keywords=("protocol", "market", "prediction", "evolution"),
        action_verbs=("predict", "trade"),
    ),
    "propagators": Skill(
        "propagators", Trit.ERGODIC, "constraint", "dataflow",
        criticality=0.8,
        keywords=("propagator", "constraint", "sussman", "dataflow"),
        action_verbs=("propagate", "constrain"),
    ),
    "autopoiesis": Skill(
        "autopoiesis", Trit.ERGODIC, "self", "modification",
        criticality=1.0,
        keywords=("autopoiesis", "self-modify", "ruler", "configure"),
        action_verbs=("configure", "modify"),
    ),
    
    # ─── PLUS (+1): Generators ───
    "skill-installer": Skill(
        "skill-installer", Trit.PLUS, "core", "installation",
        criticality=1.0,
        keywords=("install", "skill", "load", "curated"),
        action_verbs=("install", "load"),
    ),
    "gay-mcp": Skill(
        "gay-mcp", Trit.PLUS, "core", "color",
        criticality=1.0,
        keywords=("gay", "color", "splitmix", "deterministic"),
        action_verbs=("color", "generate"),
    ),
    "triad-interleave": Skill(
        "triad-interleave", Trit.PLUS, "core", "scheduling",
        criticality=0.9,
        keywords=("triad", "interleave", "stream", "parallel"),
        action_verbs=("interleave", "schedule"),
    ),
    "agent-o-rama": Skill(
        "agent-o-rama", Trit.PLUS, "learning", "training",
        criticality=0.9,
        keywords=("agent", "train", "pattern", "learn"),
        action_verbs=("train", "learn"),
    ),
    "atproto-ingest": Skill(
        "atproto-ingest", Trit.PLUS, "acquisition", "social",
        criticality=0.8,
        keywords=("atproto", "bluesky", "ingest", "social"),
        action_verbs=("fetch", "ingest"),
    ),
    "godel-machine": Skill(
        "godel-machine", Trit.PLUS, "evolution", "proof",
        criticality=1.0,
        keywords=("godel", "self-improve", "proof", "rewrite"),
        action_verbs=("prove", "rewrite"),
    ),
    "julia-gay": Skill(
        "julia-gay", Trit.PLUS, "julia", "color",
        criticality=0.9,
        keywords=("julia", "gay", "splitmix", "pigeons"),
        action_verbs=("generate", "color"),
    ),
    "mcp-builder": Skill(
        "mcp-builder", Trit.PLUS, "mcp", "server",
        criticality=1.0,
        keywords=("mcp", "server", "build", "fastmcp"),
        action_verbs=("build", "create"),
    ),
    "world-hopping": Skill(
        "world-hopping", Trit.PLUS, "navigation", "multiverse",
        criticality=0.9,
        keywords=("world", "hop", "badiou", "triangle"),
        action_verbs=("hop", "navigate"),
    ),
    "gflownet": Skill(
        "gflownet", Trit.PLUS, "learning", "sampling",
        criticality=0.8,
        keywords=("gflownet", "sample", "bengio", "reward"),
        action_verbs=("sample", "generate"),
    ),
    "forward-forward-learning": Skill(
        "forward-forward-learning", Trit.PLUS, "learning", "local",
        criticality=0.8,
        keywords=("forward-forward", "hinton", "local", "layer"),
        action_verbs=("train", "learn"),
    ),
    "curiosity-driven": Skill(
        "curiosity-driven", Trit.PLUS, "learning", "intrinsic",
        criticality=0.8,
        keywords=("curiosity", "schmidhuber", "compression", "progress"),
        action_verbs=("explore", "learn"),
    ),
    "frontend-design": Skill(
        "frontend-design", Trit.PLUS, "web", "ui",
        criticality=0.9,
        keywords=("frontend", "ui", "react", "design"),
        action_verbs=("design", "build"),
    ),
    "jaxlife-open-ended": Skill(
        "jaxlife-open-ended", Trit.PLUS, "alife", "simulation",
        criticality=0.8,
        keywords=("jaxlife", "alife", "open-ended", "emergence"),
        action_verbs=("simulate", "evolve"),
    ),
    "free-monad-gen": Skill(
        "free-monad-gen", Trit.PLUS, "functional", "dsl",
        criticality=0.7,
        keywords=("free", "monad", "dsl", "interpreter"),
        action_verbs=("generate", "interpret"),
    ),
    
    # ─── Language-Specific Skills ───
    "rust": Skill(
        "rust", Trit.ERGODIC, "language", "rust",
        keywords=("rust", "cargo", "crate"),
        action_verbs=("build", "compile"),
    ),
    "cargo-rust": Skill(
        "cargo-rust", Trit.PLUS, "rust", "package",
        keywords=("cargo", "rust", "crate", "build"),
        action_verbs=("build", "publish"),
    ),
    "python-development": Skill(
        "python-development", Trit.ERGODIC, "language", "python",
        keywords=("python", "pip", "uv", "django", "fastapi"),
        action_verbs=("develop", "run"),
    ),
    "javascript-typescript": Skill(
        "javascript-typescript", Trit.ERGODIC, "language", "javascript",
        keywords=("javascript", "typescript", "node", "react"),
        action_verbs=("develop", "build"),
    ),
    "ocaml": Skill(
        "ocaml", Trit.ERGODIC, "language", "ocaml",
        keywords=("ocaml", "dune", "merlin"),
        action_verbs=("build", "compile"),
    ),
    "clojure": Skill(
        "clojure", Trit.ERGODIC, "language", "clojure",
        keywords=("clojure", "clj", "lein", "deps"),
        action_verbs=("run", "repl"),
    ),
    "scheme": Skill(
        "scheme", Trit.ERGODIC, "language", "scheme",
        keywords=("scheme", "guile", "racket", "chicken"),
        action_verbs=("run", "evaluate"),
    ),
    "guile": Skill(
        "guile", Trit.ERGODIC, "scheme", "interpreter",
        keywords=("guile", "scheme", "gnu"),
        action_verbs=("run", "evaluate"),
    ),
    "elisp": Skill(
        "elisp", Trit.ERGODIC, "emacs", "lisp",
        keywords=("elisp", "emacs", "lisp"),
        action_verbs=("evaluate", "load"),
    ),
}

# Canonical triads from skill-dispatch
CANONICAL_TRIADS: Dict[str, Tuple[str, str, str]] = {
    "core": ("three-match", "unworld", "gay-mcp"),
    "sufficiency": ("dynamic-sufficiency", "skill-dispatch", "skill-installer"),
    "database": ("clj-kondo-3color", "acsets", "gay-mcp"),
    "learning": ("spi-parallel-verify", "cognitive-surrogate", "agent-o-rama"),
    "network": ("sheaf-cohomology", "bisimulation-game", "atproto-ingest"),
    "evolution": ("temporal-coalgebra", "self-evolving-agent", "godel-machine"),
    "repl": ("dialectica", "babashka", "mcp-builder"),
}


# ════════════════════════════════════════════════════════════════════════════
# World-Generating Memory System
# ════════════════════════════════════════════════════════════════════════════

@dataclass 
class CausalState:
    """Equivalence class of tasks with identical skill requirements."""
    domain: str
    operation: str
    complexity: str
    tool_profile: Tuple[str, ...]
    skill_signature: Tuple[str, ...]
    
    def __hash__(self):
        return hash((self.domain, self.operation, self.complexity,
                     self.tool_profile, self.skill_signature))


@dataclass
class WorldModel:
    """
    A world model generated by a skill.
    
    Each skill generates a local world model that:
    - Predicts success probability given skill configuration
    - Learns from observed outcomes
    - Provides action policies for its domain
    """
    skill: Skill
    observations: int = 0
    successes: int = 0
    causal_states: Set[CausalState] = field(default_factory=set)
    
    @property
    def success_rate(self) -> float:
        if self.observations == 0:
            return 0.5  # Uninformative prior
        return self.successes / self.observations
    
    @property
    def confidence(self) -> float:
        """Bayesian confidence based on observations."""
        # Beta distribution: higher observations → higher confidence
        return 1 - 1 / (1 + self.observations)
    
    def observe(self, state: CausalState, success: bool):
        """Update world model with observation."""
        self.observations += 1
        if success:
            self.successes += 1
        self.causal_states.add(state)
    
    def predicts_state(self, state: CausalState) -> bool:
        """Check if this world model covers the given state."""
        # Check exact match
        if state in self.causal_states:
            return True
        # Check domain/operation similarity
        for known in self.causal_states:
            if known.domain == state.domain and known.operation == state.operation:
                return True
        return False


class SkillMemory:
    """
    The memory substrate for world-generating skills.
    
    This is the self-improvising memory that:
    1. Maintains world models for each loaded skill
    2. Learns from action outcomes
    3. Infers required skills from task descriptions
    4. Supports GF(3) triadic composition
    """
    
    def __init__(self, seed: int = 0x42D):
        self.seed = seed
        self.world_models: Dict[str, WorldModel] = {}
        self.loaded_skills: Set[Skill] = set()
        self.observation_history: List[Tuple[CausalState, Set[Skill], bool]] = []
        self.inference_cache: Dict[str, Set[str]] = {}
        
        # Domain → skill mappings learned from observations
        self.domain_skill_map: Dict[str, Set[str]] = defaultdict(set)
        self.verb_skill_map: Dict[str, Set[str]] = defaultdict(set)
        
        # Initialize with registry
        self._init_from_registry()
    
    def _init_from_registry(self):
        """Initialize domain/verb mappings from skill registry."""
        for name, skill in SKILL_REGISTRY.items():
            self.domain_skill_map[skill.domain].add(name)
            for verb in skill.action_verbs:
                self.verb_skill_map[verb].add(name)
            for kw in skill.keywords:
                self.domain_skill_map[kw].add(name)
    
    def load_skill(self, skill_name: str) -> Optional[Skill]:
        """Load a skill into memory."""
        if skill_name not in SKILL_REGISTRY:
            return None
        
        skill = SKILL_REGISTRY[skill_name]
        self.loaded_skills.add(skill)
        
        # Create world model if needed
        if skill_name not in self.world_models:
            self.world_models[skill_name] = WorldModel(skill=skill)
        
        return skill
    
    def load_triad(self, bundle: str) -> Tuple[Optional[Skill], ...]:
        """Load a complete GF(3) triad."""
        if bundle not in CANONICAL_TRIADS:
            return (None, None, None)
        
        triad_names = CANONICAL_TRIADS[bundle]
        return tuple(self.load_skill(name) for name in triad_names)
    
    def infer_skills_from_text(self, text: str) -> Set[str]:
        """
        Infer required skills from natural language task description.
        
        Uses multiple signals:
        1. Keyword matching
        2. Action verb extraction
        3. Domain detection
        4. Learned associations from observations
        """
        if text in self.inference_cache:
            return self.inference_cache[text]
        
        inferred = set()
        text_lower = text.lower()
        
        # 1. Match action verbs
        for verb, skills in self.verb_skill_map.items():
            if verb in text_lower:
                inferred.update(skills)
        
        # 2. Match domains/keywords
        for domain, skills in self.domain_skill_map.items():
            if domain in text_lower:
                inferred.update(skills)
        
        # 3. Direct keyword matching from skills
        for name, skill in SKILL_REGISTRY.items():
            score = skill.matches_keywords(text)
            if score > 0.3:  # Threshold
                inferred.add(name)
        
        # 4. Language detection patterns
        lang_patterns = {
            r'\b(rust|cargo|crate)\b': ["rust", "cargo-rust"],
            r'\b(python|pip|uv|django|fastapi)\b': ["python-development"],
            r'\b(clojure|clj|babashka|bb)\b': ["clojure", "babashka"],
            r'\b(javascript|typescript|node|react)\b': ["javascript-typescript"],
            r'\b(julia|Gay\.jl)\b': ["julia-gay"],
            r'\b(ocaml|dune|opam)\b': ["ocaml", "opam-ocaml"],
            r'\b(scheme|guile|racket)\b': ["scheme", "guile"],
            r'\b(haskell|ghc|cabal|stack)\b': ["haskell"],
            r'\b(emacs|elisp)\b': ["elisp", "emacs"],
        }
        
        for pattern, skills in lang_patterns.items():
            if re.search(pattern, text_lower):
                inferred.update(skills)
        
        # 5. Operation patterns
        op_patterns = {
            r'\b(verify|check|validate|test)\b': ["spi-parallel-verify", "webapp-testing"],
            r'\b(lint|analyze)\b': ["clj-kondo-3color"],
            r'\b(install|load)\b': ["skill-installer"],
            r'\b(color|palette)\b': ["gay-mcp", "julia-gay"],
            r'\b(evolve|self-improve)\b': ["self-evolving-agent", "godel-machine"],
            r'\b(diagram|compose)\b': ["discopy"],
            r'\b(mcp|server)\b': ["mcp-builder"],
            r'\b(train|learn)\b': ["agent-o-rama", "forward-forward-learning"],
        }
        
        for pattern, skills in op_patterns.items():
            if re.search(pattern, text_lower):
                inferred.update(skills)
        
        # Cache result
        self.inference_cache[text] = inferred
        return inferred
    
    def infer_tools_from_skills(self, skills: Set[str]) -> Set[str]:
        """Infer required tools from skill set."""
        tools = set()
        
        tool_map = {
            "webapp-testing": {"Bash"},  # playwright
            "mcp-builder": {"create_file", "edit_file"},
            "babashka": {"Bash"},
            "gay-mcp": set(),  # MCP tool
            "acsets": {"Read"},
            "python-development": {"Bash", "create_file", "edit_file"},
            "rust": {"Bash"},
            "cargo-rust": {"Bash"},
        }
        
        for skill in skills:
            tools.update(tool_map.get(skill, set()))
        
        return tools
    
    def observe_outcome(self, state: CausalState, skills_used: Set[Skill], success: bool):
        """
        Update world models with observed outcome.
        
        This is the self-improvising step: learning from action results.
        """
        self.observation_history.append((state, skills_used, success))
        
        # Update each skill's world model
        for skill in skills_used:
            if skill.name in self.world_models:
                self.world_models[skill.name].observe(state, success)
        
        # Learn domain associations
        if success:
            for skill in skills_used:
                self.domain_skill_map[state.domain].add(skill.name)
    
    def complete_triad(self, skills: Set[Skill]) -> Set[Skill]:
        """
        Complete a set of skills to form a valid GF(3) triad.
        
        Ensures sum(trit) ≡ 0 (mod 3).
        """
        current_sum = sum(s.trit.value for s in skills) % 3
        
        if current_sum == 0:
            return skills
        
        # Find complementary skill
        needed = (3 - current_sum) % 3
        if needed == 2:
            needed = -1
        needed_trit = Trit(needed)
        
        # Find compatible skill from registry
        for name, skill in SKILL_REGISTRY.items():
            if skill.trit == needed_trit and skill not in skills:
                # Prefer skills in same bundle
                for s in skills:
                    if s.bundle == skill.bundle:
                        return skills | {skill}
                # Otherwise just return first match
                return skills | {skill}
        
        return skills
    
    def statistical_complexity(self) -> float:
        """
        C_μ = -Σ p(s) log₂ p(s)
        
        Entropy of the skill usage distribution.
        """
        if not self.observation_history:
            return 0.0
        
        skill_counts = Counter()
        for _, skills, _ in self.observation_history:
            for s in skills:
                skill_counts[s.name] += 1
        
        total = sum(skill_counts.values())
        probs = [c / total for c in skill_counts.values()]
        return -sum(p * log2(p) for p in probs if p > 0)
    
    def get_triad_for_task(self, task_text: str) -> Optional[Tuple[Skill, Skill, Skill]]:
        """
        Get a complete triad of skills for a task.
        
        Returns (MINUS, ERGODIC, PLUS) skills.
        """
        inferred = self.infer_skills_from_text(task_text)
        
        # Try to find skills from each trit value
        minus = None
        ergodic = None
        plus = None
        
        for name in inferred:
            if name in SKILL_REGISTRY:
                skill = SKILL_REGISTRY[name]
                if skill.trit == Trit.MINUS and minus is None:
                    minus = skill
                elif skill.trit == Trit.ERGODIC and ergodic is None:
                    ergodic = skill
                elif skill.trit == Trit.PLUS and plus is None:
                    plus = skill
        
        # Fill gaps with defaults
        if minus is None:
            minus = SKILL_REGISTRY.get("dynamic-sufficiency")
        if ergodic is None:
            ergodic = SKILL_REGISTRY.get("skill-dispatch")
        if plus is None:
            plus = SKILL_REGISTRY.get("skill-installer")
        
        return (minus, ergodic, plus) if all([minus, ergodic, plus]) else None


# ════════════════════════════════════════════════════════════════════════════
# Integration with Dynamic Sufficiency
# ════════════════════════════════════════════════════════════════════════════

class Verdict(Enum):
    PROCEED = "proceed"
    LOAD_MORE = "load_more"
    ABORT = "abort"


@dataclass
class CoverageResult:
    score: float
    is_sufficient: bool
    missing: List[Skill]
    excess: Set[Skill]
    causal_state: Optional[CausalState] = None
    triad_complete: bool = False


def pre_action_gate(
    task_text: str,
    memory: SkillMemory,
    threshold: float = 0.95
) -> Tuple[Verdict, CoverageResult]:
    """
    Gate that prevents action without sufficient skills.
    
    This is the core of dynamic-sufficiency integrated with
    the world-generating memory system.
    """
    # Infer required skills
    required_names = memory.infer_skills_from_text(task_text)
    required = {SKILL_REGISTRY[n] for n in required_names if n in SKILL_REGISTRY}
    
    # Check loaded skills
    loaded = memory.loaded_skills
    loaded_names = {s.name for s in loaded}
    required_skill_names = {s.name for s in required}
    
    # Coverage computation
    covered = loaded_names & required_skill_names
    missing_names = required_skill_names - loaded_names
    missing = [SKILL_REGISTRY[n] for n in missing_names if n in SKILL_REGISTRY]
    excess = {s for s in loaded if s.name not in required_skill_names}
    
    # Weight by criticality
    if required:
        covered_weight = sum(s.criticality for s in required if s.name in covered)
        total_weight = sum(s.criticality for s in required)
        score = covered_weight / total_weight
    else:
        score = 1.0
    
    # Check triad completion
    triad_complete = sum(s.trit.value for s in loaded) % 3 == 0 if loaded else True
    
    # Infer causal state
    tools = memory.infer_tools_from_skills(required_names)
    state = CausalState(
        domain=next((s.domain for s in required), "general"),
        operation=next((v for v in memory.verb_skill_map if v in task_text.lower()), "general"),
        complexity="O(n)",  # Could be inferred more precisely
        tool_profile=tuple(sorted(tools)),
        skill_signature=tuple(sorted(required_skill_names))
    )
    
    coverage = CoverageResult(
        score=score,
        is_sufficient=score >= threshold,
        missing=sorted(missing, key=lambda s: -s.criticality),
        excess=excess,
        causal_state=state,
        triad_complete=triad_complete
    )
    
    if coverage.is_sufficient:
        return Verdict.PROCEED, coverage
    elif score >= 0.5:
        return Verdict.LOAD_MORE, coverage
    else:
        return Verdict.ABORT, coverage


# ════════════════════════════════════════════════════════════════════════════
# Self-Improvising Loop
# ════════════════════════════════════════════════════════════════════════════

class AutopoieticLoop:
    """
    The closed autopoietic loop for self-improving skill memory.
    
    Connects:
    - dynamic-sufficiency (-1): Gates actions
    - skill-dispatch (0): Routes to triads
    - skill-installer (+1): Loads missing skills
    - world-memory: Learns from outcomes
    """
    
    def __init__(self, seed: int = 0x42D):
        self.memory = SkillMemory(seed)
        self.iteration = 0
        
        # Load core triad
        self.memory.load_triad("sufficiency")
    
    def step(self, task: str) -> Dict[str, Any]:
        """
        Execute one step of the autopoietic loop.
        
        1. Check sufficiency
        2. Load missing skills if needed (even on ABORT for learning)
        3. Execute (simulated)
        4. Observe outcome
        5. Update world models
        """
        self.iteration += 1
        
        # 1. Check sufficiency
        verdict, coverage = pre_action_gate(task, self.memory)
        
        result = {
            "iteration": self.iteration,
            "task": task,
            "verdict": verdict.value,
            "coverage": coverage.score,
            "triad_complete": coverage.triad_complete,
        }
        
        # 2. Load missing skills if needed - ALWAYS try to improve
        if verdict in (Verdict.LOAD_MORE, Verdict.ABORT) and coverage.missing:
            loaded = []
            for skill in coverage.missing[:5]:  # Load up to 5 missing skills
                if self.memory.load_skill(skill.name):
                    loaded.append(skill.name)
            result["skills_loaded"] = loaded
            
            # Re-check after loading
            verdict, coverage = pre_action_gate(task, self.memory)
            result["verdict_after_load"] = verdict.value
            result["coverage_after_load"] = coverage.score
        
        # 3. Complete triad if needed
        if not coverage.triad_complete and self.memory.loaded_skills:
            completed = self.memory.complete_triad(self.memory.loaded_skills)
            for s in completed - self.memory.loaded_skills:
                self.memory.load_skill(s.name)
            result["triad_completed"] = True
        
        # 4. Simulate execution (in real use, actual execution happens here)
        success = verdict == Verdict.PROCEED or verdict == Verdict.LOAD_MORE
        
        # 5. Observe and update
        if coverage.causal_state:
            self.memory.observe_outcome(
                coverage.causal_state,
                self.memory.loaded_skills,
                success
            )
        
        result["success"] = success
        result["complexity"] = self.memory.statistical_complexity()
        result["loaded_skills"] = [s.name for s in self.memory.loaded_skills]
        
        return result


# ════════════════════════════════════════════════════════════════════════════
# CLI Entry Point
# ════════════════════════════════════════════════════════════════════════════

# ════════════════════════════════════════════════════════════════════════════
# Semantic Skill Similarity (Fuzzy Matching)
# ════════════════════════════════════════════════════════════════════════════

def jaccard_similarity(set1: Set[str], set2: Set[str]) -> float:
    """Jaccard similarity between two sets."""
    if not set1 and not set2:
        return 1.0
    intersection = len(set1 & set2)
    union = len(set1 | set2)
    return intersection / union if union > 0 else 0.0


def skill_similarity(skill1: Skill, skill2: Skill) -> float:
    """
    Compute semantic similarity between two skills.
    
    Based on:
    - Keyword overlap
    - Domain match
    - Bundle match
    - Trit compatibility
    """
    # Keyword Jaccard
    kw_sim = jaccard_similarity(set(skill1.keywords), set(skill2.keywords))
    
    # Domain match (binary)
    domain_sim = 1.0 if skill1.domain == skill2.domain else 0.0
    
    # Bundle match (binary)
    bundle_sim = 1.0 if skill1.bundle == skill2.bundle else 0.0
    
    # Trit distance (0 if same, 0.5 if adjacent, 0 if opposite)
    trit_diff = abs(skill1.trit.value - skill2.trit.value)
    trit_sim = 1.0 if trit_diff == 0 else (0.5 if trit_diff == 1 else 0.0)
    
    # Weighted combination
    return 0.4 * kw_sim + 0.25 * domain_sim + 0.2 * bundle_sim + 0.15 * trit_sim


def find_similar_skills(
    target: Skill,
    registry: Dict[str, Skill] = SKILL_REGISTRY,
    top_k: int = 5,
    min_similarity: float = 0.2
) -> List[Tuple[str, float]]:
    """Find skills similar to target, ranked by similarity."""
    similarities = []
    for name, skill in registry.items():
        if skill.name != target.name:
            sim = skill_similarity(target, skill)
            if sim >= min_similarity:
                similarities.append((name, sim))
    
    similarities.sort(key=lambda x: -x[1])
    return similarities[:top_k]


# ════════════════════════════════════════════════════════════════════════════
# Pre-Message Hook for Agent Integration
# ════════════════════════════════════════════════════════════════════════════

@dataclass
class PreMessageResult:
    """Result from pre-message sufficiency check."""
    proceed: bool
    loaded_skills: Set[str]
    coverage: float
    missing_skills: List[str]
    suggested_triad: Optional[Tuple[str, str, str]]
    message: str


class SufficiencyHook:
    """
    Pre-message hook for agent integration.
    
    Call this before processing any user message to ensure
    sufficient skills are loaded.
    
    Usage in agent:
        hook = SufficiencyHook()
        
        def process_message(user_message):
            result = hook.pre_message(user_message)
            if not result.proceed:
                # Load suggested skills
                for skill_name in result.missing_skills[:3]:
                    load_skill(skill_name)
            # Continue processing...
    """
    
    def __init__(self, seed: int = 0x42D):
        self.loop = AutopoieticLoop(seed)
        self.message_count = 0
    
    def pre_message(self, message: str, threshold: float = 0.7) -> PreMessageResult:
        """
        Check sufficiency before processing a message.
        
        Args:
            message: The user message to process
            threshold: Minimum coverage to proceed (default 0.7 for pre-message)
        
        Returns:
            PreMessageResult with proceed flag and suggestions
        """
        self.message_count += 1
        
        # Run sufficiency check
        result = self.loop.step(message)
        coverage = result.get("coverage_after_load", result["coverage"])
        
        # Get missing skills
        _, cov_result = pre_action_gate(message, self.loop.memory, threshold)
        missing = [s.name for s in cov_result.missing]
        
        # Get suggested triad
        triad = self.loop.memory.get_triad_for_task(message)
        suggested = (triad[0].name, triad[1].name, triad[2].name) if triad else None
        
        proceed = coverage >= threshold
        
        if proceed:
            msg = f"✓ Sufficient ({coverage:.0%}). Loaded: {len(result['loaded_skills'])} skills"
        else:
            msg = f"⚠ Coverage {coverage:.0%} < {threshold:.0%}. Need: {missing[:3]}"
        
        return PreMessageResult(
            proceed=proceed,
            loaded_skills=set(result["loaded_skills"]),
            coverage=coverage,
            missing_skills=missing,
            suggested_triad=suggested,
            message=msg
        )
    
    def get_stats(self) -> Dict[str, Any]:
        """Get current memory statistics."""
        return {
            "messages_processed": self.message_count,
            "skills_loaded": len(self.loop.memory.loaded_skills),
            "world_models": len(self.loop.memory.world_models),
            "statistical_complexity": self.loop.memory.statistical_complexity(),
            "observations": len(self.loop.memory.observation_history),
        }


# ════════════════════════════════════════════════════════════════════════════
# CLI Entry Point
# ════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import sys
    
    print("╔═══════════════════════════════════════════════════════════════════╗")
    print("║  SKILLS AS WORLD-GENERATING SELF-IMPROVISING MEMORIES            ║")
    print("╚═══════════════════════════════════════════════════════════════════╝")
    
    loop = AutopoieticLoop(seed=0x42D)
    
    test_tasks = [
        "verify SPI invariance across rust and julia",
        "create an MCP server for color generation",
        "lint the clojure code and fix errors",
        "train a cognitive surrogate model",
        "evolve a self-improving agent",
    ]
    
    for task in test_tasks:
        print(f"\n─── Task: {task} ───")
        result = loop.step(task)
        print(f"  Verdict: {result['verdict']}")
        print(f"  Coverage: {result['coverage']:.1%}")
        print(f"  Triad Complete: {result['triad_complete']}")
        print(f"  Loaded: {len(result['loaded_skills'])} skills")
        print(f"  Statistical Complexity: {result['complexity']:.3f} bits")
    
    # Demo: Pre-message hook
    print("\n" + "=" * 60)
    print("PRE-MESSAGE HOOK DEMO")
    print("=" * 60)
    
    hook = SufficiencyHook(seed=0x69420)
    messages = [
        "Help me create a Julia package with deterministic colors",
        "Verify the SPI invariance holds across implementations",
    ]
    
    for msg in messages:
        print(f"\n→ \"{msg}\"")
        result = hook.pre_message(msg)
        print(f"  {result.message}")
        if result.suggested_triad:
            print(f"  Suggested triad: {result.suggested_triad}")
    
    print(f"\n─── Hook Stats ───")
    for k, v in hook.get_stats().items():
        print(f"  {k}: {v}")
    
    # Demo: Skill similarity
    print("\n" + "=" * 60)
    print("SKILL SIMILARITY DEMO")
    print("=" * 60)
    
    target = SKILL_REGISTRY["gay-mcp"]
    similar = find_similar_skills(target)
    print(f"\nSkills similar to '{target.name}':")
    for name, sim in similar:
        print(f"  {name}: {sim:.2f}")
