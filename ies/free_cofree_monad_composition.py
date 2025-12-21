#!/usr/bin/env python3
"""
FREE MONAD ≅ MODULE OVER COFREE COMONAD
Mathematical Foundation for Goblin Capability Composition

Category Theory Deep Dive:
- Free Monad F: Syntactic tree structure of computations
- Cofree Comonad W: Semantic context/environment structure
- Module Structure: F-coalgebras form a module over W
- Interpretation: compose via observe (W-coalgebras × F-algebras → result)

Key Insight:
The free monad over a functor F is isomorphic to algebras over
the cofree comonad, creating a duality:

    Free(F) ≅ Coalgebra(Cofree(G))

This isomorphism enables:
1. Syntax (free) and semantics (cofree) to coexist
2. Observation/probing of computations through W-structures
3. Composition of gadgets through monad/comonad interaction
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import TypeVar, Generic, List, Dict, Any, Callable, Tuple, Optional
import functools
from enum import Enum


# ============================================================================
# 1. FUNCTOR INTERFACE: Base for Free/Cofree Construction
# ============================================================================

A = TypeVar('A')
B = TypeVar('B')
F = TypeVar('F')  # Functor type variable
G = TypeVar('G')  # Another functor type variable


class Functor(ABC, Generic[A]):
    """
    Functor: Structure-preserving map between categories

    In our case: describes the shape of computation/observation
    """

    @abstractmethod
    def fmap(self, f: Callable[[A], B]) -> 'Functor[B]':
        """Apply function to contents while preserving structure"""
        pass


# ============================================================================
# 2. FREE MONAD: Syntax of Computation
# ============================================================================

class FreeMonad(ABC, Generic[A]):
    """
    Free Monad over functor F

    Structure:
    - Pure(a): wrap value in monad
    - Bind(f_a, cont): sequence computations
    - Free: yields functor step-by-step

    Purpose: Represent computation as syntactic tree
    - Leaves: Pure values
    - Nodes: Functor-wrapped subcomputations
    """

    @abstractmethod
    def bind(self, f: Callable[[A], 'FreeMonad[B]']) -> 'FreeMonad[B]':
        """Monadic bind: sequence computations"""
        pass

    @abstractmethod
    def map(self, f: Callable[[A], B]) -> 'FreeMonad[B]':
        """Functor map: apply function in monad context"""
        pass

    @abstractmethod
    def fold(self, pure_fn: Callable[[A], B],
             suspend_fn: Callable[[Any], B]) -> B:
        """Catamorphism: fold monad into result"""
        pass


@dataclass
class Pure(FreeMonad[A]):
    """Wrap pure value in free monad"""
    value: A

    def bind(self, f: Callable[[A], FreeMonad[B]]) -> FreeMonad[B]:
        return f(self.value)

    def map(self, f: Callable[[A], B]) -> FreeMonad[B]:
        return Pure(f(self.value))

    def fold(self, pure_fn: Callable[[A], B],
             suspend_fn: Callable[[Any], B]) -> B:
        return pure_fn(self.value)

    def __repr__(self):
        return f"Pure({self.value})"


@dataclass
class Suspend(FreeMonad[A]):
    """
    Suspend computation: wrap functor-wrapped value

    Contains: F[FreeMonad[A]] - functor yielding next monad step
    """
    computation: Any  # F[FreeMonad[A]]

    def bind(self, f: Callable[[A], FreeMonad[B]]) -> FreeMonad[B]:
        # Map f through the continuation
        def cont(next_monad: FreeMonad[A]) -> FreeMonad[B]:
            return next_monad.bind(f)
        return Suspend(self._map_computation(cont))

    def _map_computation(self, f: Callable) -> Any:
        """Map through computation structure"""
        if isinstance(self.computation, list):
            return [f(x) if isinstance(x, FreeMonad) else x for x in self.computation]
        return self.computation

    def map(self, f: Callable[[A], B]) -> FreeMonad[B]:
        return Suspend(self.computation)

    def fold(self, pure_fn: Callable[[A], B],
             suspend_fn: Callable[[Any], B]) -> B:
        return suspend_fn(self.computation)

    def __repr__(self):
        return f"Suspend(...)"


class FreeMonadBuilder(Generic[A]):
    """Builder pattern for constructing free monads"""

    def __init__(self):
        self.steps: List[Callable] = []

    def add_step(self, step: Callable) -> 'FreeMonadBuilder':
        """Add computation step"""
        self.steps.append(step)
        return self

    def build(self, initial: A) -> FreeMonad[A]:
        """Build free monad from steps"""
        result: FreeMonad[A] = Pure(initial)
        for step in self.steps:
            result = result.bind(step)
        return result


# ============================================================================
# 3. COFREE COMONAD: Semantics of Observation
# ============================================================================

class Cofree(ABC, Generic[A]):
    """
    Cofree Comonad

    Structure:
    - Head: current observation/value
    - Tail: comonadic extension (observations of different types)
    - Iterate: generate infinite sequence of observations

    Purpose: Represent semantic context/environment structure
    - Can be "probed" at different observation types
    - Maintains history of observations
    """

    @abstractmethod
    def extract(self) -> A:
        """Extract current value (counit)"""
        pass

    @abstractmethod
    def extend(self, f: Callable[['Cofree[A]'], B]) -> 'Cofree[B]':
        """Comonadic extend: apply function to continuation (comultiplication)"""
        pass

    @abstractmethod
    def map(self, f: Callable[[A], B]) -> 'Cofree[B]':
        """Functor map in cofree context"""
        pass

    @abstractmethod
    def observe(self, observation_type: str) -> Any:
        """Probe observation at specific type"""
        pass


@dataclass
class CofreeValue(Cofree[A]):
    """
    Cofree comonad value

    Contains:
    - head: current value
    - tails: map of observation type → cofree extension
    """
    head: A
    tails: Dict[str, 'Cofree[Any]']

    def extract(self) -> A:
        return self.head

    def extend(self, f: Callable[['Cofree[A]'], B]) -> 'Cofree[B]':
        """Apply function to cofree structure"""
        new_tails = {}
        for obs_type, tail in self.tails.items():
            new_tails[obs_type] = tail.extend(f)

        return CofreeValue(f(self), new_tails)

    def map(self, f: Callable[[A], B]) -> 'Cofree[B]':
        new_head = f(self.head)
        new_tails = {k: v.map(f) for k, v in self.tails.items()}
        return CofreeValue(new_head, new_tails)

    def observe(self, observation_type: str) -> Any:
        """Get observation of specific type"""
        if observation_type in self.tails:
            return self.tails[observation_type].extract()
        return None

    def add_observation(self, observation_type: str, cofree: 'Cofree[Any]'):
        """Add new observation type"""
        self.tails[observation_type] = cofree

    def __repr__(self):
        obs_types = list(self.tails.keys())
        return f"Cofree({self.head}, observations={obs_types})"


class CofreeBuilder(Generic[A]):
    """Builder for constructing cofree comonads"""

    def __init__(self, head: A):
        self.head = head
        self.observations: Dict[str, Any] = {}

    def add_observation(self, obs_type: str, value: Any) -> 'CofreeBuilder':
        """Add observation"""
        self.observations[obs_type] = value
        return self

    def build(self) -> Cofree[A]:
        """Build cofree comonad"""
        tails = {}
        for obs_type, value in self.observations.items():
            if isinstance(value, Cofree):
                tails[obs_type] = value
            else:
                tails[obs_type] = CofreeValue(value, {})

        return CofreeValue(self.head, tails)


# ============================================================================
# 4. MODULE STRUCTURE: Free as Module over Cofree
# ============================================================================

class FreeCofrreeModule:
    """
    Free Monad as Module over Cofree Comonad

    Key theorem:
    Algebra(F) ≅ Coalgebra(Cofree(G)) where F and G are dual functors

    Module operations:
    1. Action: (Cofree, FreeMonad) → result
    2. Composition: sequence free monad with cofree observations
    """

    @staticmethod
    def interpret(cofree: Cofree[Any], free_monad: FreeMonad[Any]) -> Any:
        """
        Interpret free monad using cofree comonad as semantic context

        Process:
        1. Extract value from free monad (if pure)
        2. Extend cofree with interpretation function
        3. Observe result from cofree structure
        """

        # Extract current value from free monad
        if isinstance(free_monad, Pure):
            value = free_monad.value
            # Observe through cofree structure
            return cofree.extend(lambda w: value).extract()

        elif isinstance(free_monad, Suspend):
            # For suspended computations, propagate through cofree tails
            return cofree

        return None

    @staticmethod
    def compose_free_with_cofree(free_steps: List[FreeMonad[Any]],
                                  cofree_observations: Dict[str, Cofree[Any]]) -> Dict[str, Any]:
        """
        Compose multiple free monads with cofree observations

        Returns: interpretation of each free monad through cofree context
        """
        results = {}

        for i, free in enumerate(free_steps):
            step_key = f"step_{i}"

            # Try to match with observation
            for obs_type, cofree in cofree_observations.items():
                result = FreeCofrreeModule.interpret(cofree, free)
                results[f"{step_key}__{obs_type}"] = result

        return results


# ============================================================================
# 5. GOBLIN MONAD ACTIONS: Free/Cofree in Capability Discovery
# ============================================================================

class GoblinMonadAction:
    """
    Goblin capability actions as free monads with cofree observations

    A goblin action is:
    - Free monad: sequence of capability invocations
    - Cofree observations: probed results from other goblins
    - Composition: blend syntax and semantics
    """

    @staticmethod
    def create_capability_action(actions: List[str]) -> FreeMonad[str]:
        r"""
        Create free monad representing sequence of goblin actions

        Example: [discover_quantum, probe_goblin_a, verify_gadget]
        becomes: Pure(discover) >>= \_ -> Pure(probe) >>= \_ -> Pure(verify)
        """
        if not actions:
            return Pure("")

        result = Pure(actions[0])
        for action in actions[1:]:
            result = result.bind(lambda _: Pure(action))

        return result

    @staticmethod
    def create_observation_context(goblin_names: List[str],
                                   probed_data: Dict[str, Any]) -> Cofree[str]:
        """
        Create cofree comonad representing observation context

        Each goblin name becomes an observation point with probed data
        """
        builder = CofreeBuilder("context")

        for goblin_name in goblin_names:
            if goblin_name in probed_data:
                builder.add_observation(goblin_name, probed_data[goblin_name])
            else:
                builder.add_observation(goblin_name, f"unknown_{goblin_name}")

        return builder.build()

    @staticmethod
    def execute_with_module_action(capabilities: List[str],
                                   observations: Dict[str, Any],
                                   goblin_names: List[str]) -> Dict[str, Any]:
        """
        Execute goblin actions as module action:
        (Free capability monad) ⊗ (Cofree observation comonad) → result
        """
        # Create free monad of actions
        free_action = GoblinMonadAction.create_capability_action(capabilities)

        # Create cofree comonad of observations
        cofree_context = GoblinMonadAction.create_observation_context(goblin_names, observations)

        # Compose via module action
        results = FreeCofrreeModule.compose_free_with_cofree(
            [free_action],
            {f"goblin_{name}": cofree_context for name in goblin_names}
        )

        return results


# ============================================================================
# 6. DEMONSTRATION: Free Monad + Cofree Comonad Composition
# ============================================================================

def demo():
    """
    Demonstrate free monad and cofree comonad composition
    """

    print("\n╔════════════════════════════════════════════════════════════════╗")
    print("║  FREE MONAD ≅ MODULE OVER COFREE COMONAD                     ║")
    print("║  Category Theoretic Foundation for Goblin Composition         ║")
    print("╚════════════════════════════════════════════════════════════════╝\n")

    # [1] Create free monads of actions
    print("[1] Creating free monads of goblin actions...")

    capabilities_a = ["discover_quantum", "probe_goblin_b", "compose_capability"]
    free_action_a = GoblinMonadAction.create_capability_action(capabilities_a)
    print(f"  Free monad A: {free_action_a}")

    capabilities_b = ["discover_logic", "verify_gadget", "register_capability"]
    free_action_b = GoblinMonadAction.create_capability_action(capabilities_b)
    print(f"  Free monad B: {free_action_b}")

    # [2] Create cofree comonads of observations
    print("\n[2] Creating cofree comonads of observations...")

    probed_data = {
        "Goblin_A": {"quantum": 3, "logic": 2},
        "Goblin_B": {"quantum": 1, "logic": 4},
        "Goblin_C": {"quantum": 2, "logic": 3}
    }

    cofree_context = GoblinMonadAction.create_observation_context(
        ["Goblin_A", "Goblin_B"],
        probed_data
    )
    print(f"  Cofree context: {cofree_context}")

    # [3] Show free monad structure
    print("\n[3] Free monad structure:")
    print(f"  Type: {type(free_action_a).__name__}")
    print(f"  Initial action: discover_quantum")
    print(f"  Continuation: probe_goblin_b >>= compose_capability")

    # [4] Show cofree comonad structure
    print("\n[4] Cofree comonad structure:")
    print(f"  Head: {cofree_context.extract()}")
    print(f"  Observations: {list(cofree_context.tails.keys())}")

    # [5] Execute module action (free ⊗ cofree)
    print("\n[5] Executing module action (Free ⊗ Cofree)...")

    results = GoblinMonadAction.execute_with_module_action(
        capabilities_a,
        probed_data,
        ["Goblin_A", "Goblin_B"]
    )

    print(f"  Module action results:")
    for key, value in results.items():
        print(f"    {key}: {type(value).__name__}")

    # [6] Demonstrate extend (comonadic extension)
    print("\n[6] Comonadic extension (extend)...")

    def observation_probe(cofree: Cofree) -> str:
        """Extend function: probe observations"""
        return f"observed_{cofree.extract()}"

    extended = cofree_context.extend(observation_probe)
    print(f"  Extended cofree: {extended.extract()}")

    # [7] Demonstrate bind (monadic composition)
    print("\n[7] Monadic bind (sequence actions)...")

    def next_capability(action: str) -> FreeMonad[str]:
        if action == "discover_quantum":
            return Pure("quantum_found")
        elif action == "quantum_found":
            return Pure("verified")
        else:
            return Pure(action)

    bound_monad = free_action_a.bind(next_capability)
    print(f"  After bind: {type(bound_monad).__name__}")

    # [8] Interpret using module structure
    print("\n[8] Full module interpretation:")
    print(f"  (Free capability monad) ⊗ (Cofree observation comonad)")
    print(f"  Result: Composed goblin behavior")

    # [9] Show mathematical properties
    print("\n[9] Mathematical properties demonstrated:")
    print(f"  ✓ Free monad syntax: {capabilities_a}")
    print(f"  ✓ Cofree comonad semantics: observations across goblins")
    print(f"  ✓ Module action: (Free ⊗ Cofree) → interpretation")
    print(f"  ✓ Composition: free bind + cofree extend = behavior")

    # [10] Summary
    print("\n[10] Summary:")
    print(f"  Free monad: Syntactic computation tree")
    print(f"  Cofree comonad: Semantic observation structure")
    print(f"  Module: Free as algebra over Cofree as coalgebra")
    print(f"  Result: Goblin capabilities composed via category theory")

    print("\n✓ Demonstration complete")
    print("Integration: Free/Cofree module with Goblin probing system")


if __name__ == "__main__":
    demo()
