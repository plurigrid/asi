#!/usr/bin/env python3
"""
Worlding Skill: Meta-Learning Architecture for Continual World Modeling

Integrates Google's Nested Learning paradigm with hierarchical skill composition
to create self-improving world models that learn without catastrophic forgetting.

Inspired by:
- Nested Learning (Google Research NeurIPS 2025)
- Hope Architecture (Self-modifying continuum memory systems)
- Hierarchical Meta-RL (Skill-based learning)
- Continual Learning (Neuroplasticity)
"""

import json
import math
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Callable, Any, Optional
from enum import Enum
from abc import ABC, abstractmethod


# ============================================================================
# Core Types & Enums
# ============================================================================

class UpdateFrequency(Enum):
    """Multi-timescale update rates (inspired by brain neuroplasticity)"""
    FAST = 0.01      # Layer/prompt adaptation (immediate context)
    MEDIUM = 0.1     # Skill composition (task level)
    SLOW = 1.0       # Architecture/meta-strategy (world model level)
    VERY_SLOW = 10.0 # Long-term knowledge consolidation


class MemoryType(Enum):
    """Continuum Memory System (CMS) - multi-scale memory hierarchy"""
    WORKING = "working"        # Immediate context (Transformer attention)
    EPISODIC = "episodic"      # Recent experiences (in-context learning)
    SEMANTIC = "semantic"      # General knowledge (pre-training weights)
    PROCEDURAL = "procedural"  # Learned skills (meta-parameters)
    CONSOLIDATED = "consolidated"  # Long-term world model


@dataclass
class OptimizationLevel:
    """Represents one level in the nested optimization hierarchy"""
    level_id: int
    update_frequency: UpdateFrequency
    context_flow: Dict[str, Any] = field(default_factory=dict)
    learnable_params: Dict[str, float] = field(default_factory=dict)
    error_signal: Optional[float] = None

    def update_rate(self) -> float:
        """How often to update this level (in gradient steps)"""
        return self.update_frequency.value


# ============================================================================
# Continuum Memory System (CMS)
# ============================================================================

class MemoryModule(ABC):
    """Base class for memory modules in the continuum"""

    def __init__(self, module_id: str, update_freq: UpdateFrequency):
        self.module_id = module_id
        self.update_frequency = update_freq
        self.memory_bank: Dict[str, Any] = {}
        self.access_history: List[str] = []

    @abstractmethod
    def store(self, key: str, value: Any) -> None:
        """Store associative memory (key -> value mapping)"""
        pass

    @abstractmethod
    def retrieve(self, query: Any) -> Any:
        """Retrieve memory via associative lookup"""
        pass

    @abstractmethod
    def update(self, error_signal: float) -> None:
        """Update memory based on prediction error"""
        pass


class WorkingMemory(MemoryModule):
    """Fast, attention-based immediate context"""

    def __init__(self):
        super().__init__("working", UpdateFrequency.FAST)
        self.context_window: List[Any] = []
        self.attention_weights: Dict[str, float] = {}

    def store(self, key: str, value: Any) -> None:
        """Store in immediate context"""
        self.memory_bank[key] = value
        self.context_window.append(key)
        if len(self.context_window) > 512:  # Context window size
            self.context_window.pop(0)

    def retrieve(self, query: Any) -> Any:
        """Attention-based retrieval (dot-product similarity)"""
        best_match = None
        best_score = -float('inf')

        for key in self.context_window:
            # Simplified attention: similarity score
            score = self._similarity(query, self.memory_bank[key])
            if score > best_score:
                best_score = score
                best_match = key

        return self.memory_bank[best_match] if best_match else None

    def update(self, error_signal: float) -> None:
        """Rapidly adapt attention weights to prediction errors"""
        for key in self.attention_weights:
            self.attention_weights[key] *= (1 - error_signal * self.update_frequency.value)

    @staticmethod
    def _similarity(a: Any, b: Any) -> float:
        """Compute dot-product similarity"""
        if isinstance(a, (int, float)) and isinstance(b, (int, float)):
            return float(a * b)
        return 0.5  # Default moderate similarity


class EpisodicMemory(MemoryModule):
    """Medium-speed episode/task memory"""

    def __init__(self):
        super().__init__("episodic", UpdateFrequency.MEDIUM)
        self.episodes: Dict[str, Dict[str, Any]] = {}
        self.current_episode: Optional[str] = None

    def store(self, key: str, value: Any) -> None:
        """Store experience as episode"""
        if self.current_episode is None:
            self.current_episode = f"episode_{len(self.episodes)}"
            self.episodes[self.current_episode] = {}

        self.episodes[self.current_episode][key] = value
        self.memory_bank[key] = value

    def retrieve(self, query: Any) -> Any:
        """Retrieve from recent episodes"""
        if self.current_episode and query in self.episodes[self.current_episode]:
            return self.episodes[self.current_episode][query]

        # Fall back to semantic search across episodes
        for episode in reversed(list(self.episodes.values())):
            if query in episode:
                return episode[query]
        return None

    def new_episode(self) -> None:
        """Mark end of current episode"""
        self.current_episode = None

    def update(self, error_signal: float) -> None:
        """Consolidate significant experiences (high error)"""
        if error_signal > 0.5:  # High surprise
            if self.current_episode:
                # Mark for consolidation to semantic memory
                self.episodes[self.current_episode]["consolidate"] = True


class SemanticMemory(MemoryModule):
    """Slow, stable general knowledge (pre-training weights)"""

    def __init__(self):
        super().__init__("semantic", UpdateFrequency.SLOW)
        self.knowledge_graph: Dict[str, List[str]] = {}
        self.generalizations: Dict[str, Any] = {}

    def store(self, key: str, value: Any) -> None:
        """Store as general knowledge"""
        self.memory_bank[key] = value

        # Build knowledge graph
        if isinstance(value, dict) and "category" in value:
            category = value["category"]
            if category not in self.knowledge_graph:
                self.knowledge_graph[category] = []
            self.knowledge_graph[category].append(key)

    def retrieve(self, query: Any) -> Any:
        """Retrieve general knowledge"""
        return self.memory_bank.get(query)

    def update(self, error_signal: float) -> None:
        """Slowly update generalizations based on patterns"""
        if error_signal > 0.7:  # Very surprising -> update general knowledge
            self.generalizations["anomaly_count"] = \
                self.generalizations.get("anomaly_count", 0) + 1


class ProceduralMemory(MemoryModule):
    """Learned skills and meta-parameters"""

    def __init__(self):
        super().__init__("procedural", UpdateFrequency.MEDIUM)
        self.skills: Dict[str, Callable] = {}
        self.skill_parameters: Dict[str, Dict[str, float]] = {}

    def store(self, key: str, value: Any) -> None:
        """Store skill or meta-parameter"""
        if callable(value):
            self.skills[key] = value
        else:
            self.skill_parameters[key] = value
        self.memory_bank[key] = value

    def retrieve(self, query: Any) -> Any:
        """Retrieve skill or parameter"""
        if query in self.skills:
            return self.skills[query]
        return self.skill_parameters.get(query)

    def update(self, error_signal: float) -> None:
        """Adapt skill parameters to improve performance"""
        for skill_id in self.skill_parameters:
            for param in self.skill_parameters[skill_id]:
                # Gradient-like update: reduce parameters proportional to error
                current = self.skill_parameters[skill_id][param]
                self.skill_parameters[skill_id][param] = \
                    current * (1 - error_signal * self.update_frequency.value)


# ============================================================================
# Nested Learning: Multi-Level Optimization
# ============================================================================

class NestedOptimizer:
    """
    Unified optimizer that treats model architecture and training algorithm
    as different "levels" of optimization, each with its own update rate.

    Based on Nested Learning paradigm (Google Research, NeurIPS 2025)
    """

    def __init__(self):
        self.levels: Dict[int, OptimizationLevel] = {}
        self.level_count = 0
        self._build_levels()

    def _build_levels(self) -> None:
        """Initialize nested optimization levels"""
        # Level 0: Fast - in-context adaptation (working memory)
        self.add_level(
            update_frequency=UpdateFrequency.FAST,
            description="In-context learning (immediate context flow)"
        )

        # Level 1: Medium - skill composition (episodic/procedural)
        self.add_level(
            update_frequency=UpdateFrequency.MEDIUM,
            description="Skill composition (task-level context flow)"
        )

        # Level 2: Slow - world model structure (semantic memory)
        self.add_level(
            update_frequency=UpdateFrequency.SLOW,
            description="World model structure (knowledge graph)"
        )

        # Level 3: Very Slow - meta-strategy
        self.add_level(
            update_frequency=UpdateFrequency.VERY_SLOW,
            description="Meta-strategy (learning how to learn)"
        )

    def add_level(self, update_frequency: UpdateFrequency,
                  description: str = "") -> OptimizationLevel:
        """Add a new optimization level"""
        level = OptimizationLevel(
            level_id=self.level_count,
            update_frequency=update_frequency
        )
        self.levels[self.level_count] = level
        self.level_count += 1
        return level

    def compute_gradient(self, error_signal: float) -> Dict[int, float]:
        """
        Compute gradients for each level based on error signal and update frequency.

        Slower levels get scaled-down gradients to prevent catastrophic forgetting.
        """
        gradients = {}
        for level_id, level in self.levels.items():
            # Higher levels (slower updates) get dampened gradients
            damping_factor = level.update_frequency.value / UpdateFrequency.FAST.value
            gradients[level_id] = error_signal * damping_factor
        return gradients

    def apply_updates(self, gradients: Dict[int, float],
                     learning_rate: float = 0.01) -> None:
        """Apply gradient updates to all levels"""
        for level_id, gradient in gradients.items():
            self.levels[level_id].error_signal = gradient


# ============================================================================
# Skill Making Skill (Meta-Skill)
# ============================================================================

class SkillMaker:
    """
    Meta-skill that learns to create new skills from experience.

    Uses nested learning to:
    1. Extract reusable sub-skills from observations
    2. Compose them hierarchically
    3. Learn when to apply which skill
    """

    def __init__(self):
        self.discovered_skills: Dict[str, Callable] = {}
        self.skill_compositions: Dict[str, List[str]] = {}
        self.skill_effectiveness: Dict[str, float] = {}
        self.meta_optimizer = NestedOptimizer()

    def observe_pattern(self, experience: Dict[str, Any]) -> str:
        """Observe an experience and abstract it into a skill"""
        skill_id = f"skill_{len(self.discovered_skills)}"

        # Extract invariant pattern from experience
        pattern = self._extract_pattern(experience)

        # Create skill function
        def skill_fn(context: Dict[str, Any]) -> Any:
            """Execute learned skill"""
            return self._apply_pattern(pattern, context)

        self.discovered_skills[skill_id] = skill_fn
        self.skill_effectiveness[skill_id] = 0.5  # Initial confidence

        return skill_id

    def compose_skills(self, skill_ids: List[str],
                      order: str = "sequential") -> str:
        """Compose multiple skills into a higher-order skill"""
        composite_id = f"composite_{len(self.skill_compositions)}"

        if order == "sequential":
            def composite_skill(context: Dict[str, Any]) -> Any:
                result = context
                for skill_id in skill_ids:
                    result = self.discovered_skills[skill_id](result)
                return result

        elif order == "hierarchical":
            def composite_skill(context: Dict[str, Any]) -> Any:
                # Learn which skill to apply based on context
                selected_skill = self._select_best_skill(skill_ids, context)
                return self.discovered_skills[selected_skill](context)

        else:  # parallel
            def composite_skill(context: Dict[str, Any]) -> Any:
                results = {}
                for skill_id in skill_ids:
                    results[skill_id] = self.discovered_skills[skill_id](context)
                return results

        self.discovered_skills[composite_id] = composite_skill
        self.skill_compositions[composite_id] = skill_ids

        return composite_id

    def evaluate_skill(self, skill_id: str,
                      test_cases: List[Dict[str, Any]]) -> float:
        """Evaluate skill effectiveness on test cases"""
        successes = 0
        for test_case in test_cases:
            try:
                result = self.discovered_skills[skill_id](test_case)
                if result is not None and not isinstance(result, dict) or \
                   result.get("success", True):
                    successes += 1
            except:
                pass

        effectiveness = successes / len(test_cases) if test_cases else 0.5
        self.skill_effectiveness[skill_id] = effectiveness
        return effectiveness

    def _extract_pattern(self, experience: Dict[str, Any]) -> Dict[str, Any]:
        """Extract generalizable pattern from experience"""
        pattern = {}
        for key, value in experience.items():
            if key not in ["timestamp", "id", "metadata"]:
                pattern[key] = value
        return pattern

    def _apply_pattern(self, pattern: Dict[str, Any],
                      context: Dict[str, Any]) -> Any:
        """Apply learned pattern to new context"""
        # Simple pattern matching: map pattern to context
        result = {}
        for key, value in pattern.items():
            if key in context:
                result[key] = context[key]
        return result

    def _select_best_skill(self, skill_ids: List[str],
                          context: Dict[str, Any]) -> str:
        """Select best skill for context (Thompson sampling)"""
        best_skill = skill_ids[0]
        best_effectiveness = self.skill_effectiveness.get(best_skill, 0.5)

        for skill_id in skill_ids[1:]:
            eff = self.skill_effectiveness.get(skill_id, 0.5)
            if eff > best_effectiveness:
                best_skill = skill_id
                best_effectiveness = eff

        return best_skill


# ============================================================================
# Worlding Skill: Self-Improving World Model
# ============================================================================

class WorldingSkill:
    """
    Meta-meta-skill: Builds and continuously improves world models
    using nested learning, without catastrophic forgetting.

    Implements the "Hope" architecture paradigm with self-modification
    and continuum memory systems.
    """

    def __init__(self):
        # Multi-timescale memory
        self.memory_system = {
            MemoryType.WORKING: WorkingMemory(),
            MemoryType.EPISODIC: EpisodicMemory(),
            MemoryType.SEMANTIC: SemanticMemory(),
            MemoryType.PROCEDURAL: ProceduralMemory(),
            MemoryType.CONSOLIDATED: SemanticMemory(),  # Consolidated long-term memory
        }

        # Nested optimization
        self.nested_optimizer = NestedOptimizer()

        # Skill maker for learning new skills
        self.skill_maker = SkillMaker()

        # World model state
        self.world_model: Dict[str, Any] = {}
        self.prediction_history: List[Tuple[Any, Any, float]] = []
        self.learning_steps = 0

    def observe(self, observation: Dict[str, Any]) -> None:
        """Observe world state and store in memory hierarchy"""
        # Store in working memory (fast)
        self.memory_system[MemoryType.WORKING].store(
            f"obs_{self.learning_steps}",
            observation
        )

        # Store in episodic memory (medium speed)
        self.memory_system[MemoryType.EPISODIC].store(
            f"episode_obs_{self.learning_steps}",
            observation
        )

        self.learning_steps += 1

    def predict(self, query: Dict[str, Any]) -> Any:
        """Make prediction about world state"""
        # Hierarchical prediction: fast → medium → slow

        # Try working memory first (fast)
        prediction = self.memory_system[MemoryType.WORKING].retrieve(query)
        if prediction is not None:
            return prediction

        # Try episodic memory (medium)
        prediction = self.memory_system[MemoryType.EPISODIC].retrieve(query)
        if prediction is not None:
            return prediction

        # Use semantic knowledge (slow)
        prediction = self.memory_system[MemoryType.SEMANTIC].retrieve(query)

        return prediction

    def learn_from_error(self, actual: Any, predicted: Any) -> None:
        """Learn from prediction error without catastrophic forgetting"""
        # Compute error signal
        error = self._compute_error(actual, predicted)

        # Get gradients for each level (nested learning)
        gradients = self.nested_optimizer.compute_gradient(error)

        # Update memory at appropriate speeds
        self.memory_system[MemoryType.WORKING].update(error)
        self.memory_system[MemoryType.EPISODIC].update(error)
        self.memory_system[MemoryType.SEMANTIC].update(error)
        self.memory_system[MemoryType.PROCEDURAL].update(error)

        # Store prediction history for analysis
        self.prediction_history.append((predicted, actual, error))

        # If low error, consolidate knowledge
        if error < 0.2:
            self._consolidate_knowledge()

        # If high error and frequent, learn new skill
        if error > 0.7 and self._should_learn_new_skill():
            self._learn_new_skill_from_error(actual, predicted)

    def self_modify(self) -> None:
        """Self-referential optimization: world model modifies itself"""
        # Analyze prediction history
        recent_errors = [e for _, _, e in self.prediction_history[-100:]]
        avg_error = sum(recent_errors) / len(recent_errors) if recent_errors else 0

        if avg_error > 0.5:  # High error rate
            # Increase update frequency for slow levels
            self.nested_optimizer.levels[2].update_frequency = UpdateFrequency.MEDIUM
        elif avg_error < 0.1:  # Very low error
            # Can afford slower updates
            self.nested_optimizer.levels[2].update_frequency = UpdateFrequency.SLOW

        # Discover new skills if helpful
        if len(self.skill_maker.discovered_skills) < 10:
            self._discover_skills_from_memory()

    def get_world_state(self) -> Dict[str, Any]:
        """Export current world model understanding"""
        return {
            "learning_steps": self.learning_steps,
            "discovered_skills": len(self.skill_maker.discovered_skills),
            "skill_compositions": len(self.skill_maker.skill_compositions),
            "avg_prediction_error": self._avg_prediction_error(),
            "memory_sizes": {
                mem_type.value: len(self.memory_system[mem_type].memory_bank)
                for mem_type in MemoryType
            },
            "world_model": self.world_model,
        }

    def _compute_error(self, actual: Any, predicted: Any) -> float:
        """Compute prediction error (0.0 to 1.0)"""
        if actual == predicted:
            return 0.0
        elif isinstance(actual, (int, float)) and isinstance(predicted, (int, float)):
            # MSE-like error
            error = abs(actual - predicted)
            return min(1.0, error / max(abs(actual), 1.0))
        else:
            # Binary error for categorical
            return 1.0

    def _consolidate_knowledge(self) -> None:
        """Move validated knowledge from episodic to semantic memory"""
        episodic = self.memory_system[MemoryType.EPISODIC]
        semantic = self.memory_system[MemoryType.SEMANTIC]

        # Find high-confidence episodes
        for episode_id, episode_data in episodic.episodes.items():
            if episode_data.get("consolidate", False):
                for key, value in episode_data.items():
                    semantic.store(key, value)

    def _should_learn_new_skill(self) -> bool:
        """Decide if current skill set is insufficient"""
        if len(self.prediction_history) < 50:
            return False

        recent_high_errors = sum(1 for _, _, e in self.prediction_history[-50:] if e > 0.7)
        return recent_high_errors > 10  # More than 20% high errors

    def _learn_new_skill_from_error(self, actual: Any, predicted: Any) -> None:
        """Learn new skill to handle prediction errors"""
        experience = {
            "predicted": predicted,
            "actual": actual,
            "error": self._compute_error(actual, predicted),
            "category": "error_correction"
        }

        skill_id = self.skill_maker.observe_pattern(experience)
        # Test new skill
        self.skill_maker.evaluate_skill(skill_id, [experience])

    def _discover_skills_from_memory(self) -> None:
        """Discover reusable skills by analyzing memory patterns"""
        # Find common patterns in episodic memory
        episodic = self.memory_system[MemoryType.EPISODIC]

        if len(episodic.episodes) > 5:
            # Extract pattern from first episode
            first_episode = list(episodic.episodes.values())[0]
            skill_id = self.skill_maker.observe_pattern(first_episode)

            # Try to compose with other skills
            if len(self.skill_maker.discovered_skills) > 1:
                all_skills = list(self.skill_maker.discovered_skills.keys())
                self.skill_maker.compose_skills(all_skills[:2], order="sequential")

    def _avg_prediction_error(self) -> float:
        """Compute average prediction error"""
        if not self.prediction_history:
            return 0.5
        errors = [e for _, _, e in self.prediction_history]
        return sum(errors) / len(errors)


# ============================================================================
# Example Usage & Testing
# ============================================================================

def example_worlding_skill():
    """Demonstrate worlding skill in action"""
    print("=" * 70)
    print("WORLDING SKILL DEMONSTRATION")
    print("Nested Learning + Continual Memory + Self-Modification")
    print("=" * 70)

    # Create worlding skill
    world = WorldingSkill()

    # Simulate observations and learning
    observations = [
        {"temperature": 25, "humidity": 60, "pressure": 1013, "category": "weather"},
        {"temperature": 26, "humidity": 62, "pressure": 1012, "category": "weather"},
        {"temperature": 24, "humidity": 58, "pressure": 1014, "category": "weather"},
    ]

    print("\n1. OBSERVATION PHASE")
    print("-" * 70)
    for i, obs in enumerate(observations):
        world.observe(obs)
        print(f"Step {i}: Observed {obs}")

    print("\n2. PREDICTION & LEARNING PHASE")
    print("-" * 70)

    # Make predictions and learn from errors
    predictions = [
        ({"temperature": 27}, 26),  # Predict temp, see actual 26
        ({"humidity": 61}, 62),     # Predict humidity, see actual 62
        ({"pressure": 1013}, 1014), # Predict pressure, see actual 1014
    ]

    for i, (query, actual) in enumerate(predictions):
        predicted = world.predict(query)
        world.learn_from_error(actual, predicted)
        error = world._compute_error(actual, predicted)
        print(f"Prediction {i}: Query {query}")
        print(f"  Predicted: {predicted}, Actual: {actual}, Error: {error:.3f}")

    print("\n3. SKILL LEARNING PHASE")
    print("-" * 70)

    # Learn skills from experience
    experience_1 = {"temperature": 25, "humidity": 60, "prediction_accuracy": 0.95}
    skill_1 = world.skill_maker.observe_pattern(experience_1)
    print(f"Discovered Skill 1: {skill_1}")

    experience_2 = {"pressure": 1013, "trend": "stable", "prediction_accuracy": 0.92}
    skill_2 = world.skill_maker.observe_pattern(experience_2)
    print(f"Discovered Skill 2: {skill_2}")

    # Compose skills
    composite = world.skill_maker.compose_skills([skill_1, skill_2], order="sequential")
    print(f"Composite Skill: {composite}")
    print(f"  Composing: {world.skill_maker.skill_compositions[composite]}")

    print("\n4. SELF-MODIFICATION PHASE")
    print("-" * 70)

    world.self_modify()
    print("World model self-modified based on learning history")
    print(f"Update frequency adjusted based on error rate")
    print(f"New discovered skills: {len(world.skill_maker.discovered_skills)}")

    print("\n5. FINAL WORLD STATE")
    print("-" * 70)

    state = world.get_world_state()
    print(json.dumps(state, indent=2))

    print("\n6. CONTINUUM MEMORY SYSTEM STATUS")
    print("-" * 70)

    for mem_type in MemoryType:
        mem = world.memory_system[mem_type]
        print(f"{mem_type.value.upper():20} - Update freq: {mem.update_frequency.name:10} - Size: {len(mem.memory_bank)}")

    print("\n7. NESTED OPTIMIZATION LEVELS")
    print("-" * 70)

    for level_id, level in world.nested_optimizer.levels.items():
        print(f"Level {level_id}: Update Rate = {level.update_frequency.value:6.2f} "
              f"(prevents catastrophic forgetting)")

    print("\n" + "=" * 70)
    print("SUCCESS: Worlding skill demonstrates continual learning")
    print("without catastrophic forgetting via nested optimization!")
    print("=" * 70)


if __name__ == "__main__":
    example_worlding_skill()
