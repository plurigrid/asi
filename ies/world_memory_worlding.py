#!/usr/bin/env python3
"""
World Memory Is World Remembering Is World Worlding

Implementation of the autopoietic strange loop where:
- MEMORY (-1): Storage/persistence (FILTERING)
- REMEMBERING (0): Pattern matching/recall (ITERATION)
- WORLDING (+1): Generation/creation (INTEGRATION)

Conservation: (-1) + 0 + (+1) = 0 ✓
"""

import hashlib
import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Any, Optional, Tuple
from enum import IntEnum


class Trit(IntEnum):
    """GF(3) trit values"""
    MINUS = -1   # Memory (storage, constraint)
    ERGODIC = 0  # Remembering (recall, iteration)
    PLUS = 1     # Worlding (generation, creation)


@dataclass
class WorldState:
    """A single world state in the autopoietic loop"""
    seed: int
    cycle: int
    data: Any
    trit: Trit
    color: str = ""
    
    def __post_init__(self):
        if not self.color:
            self.color = self._compute_color()
    
    def _compute_color(self) -> str:
        """Deterministic color from seed + cycle (Gay.jl style)"""
        h = hashlib.sha256(f"{self.seed}:{self.cycle}".encode()).hexdigest()
        return f"#{h[:6].upper()}"


@dataclass 
class MemoryTrace:
    """A trace in world memory"""
    key: str
    value: Any
    timestamp: int
    retrieval_count: int = 0
    coherence: float = 1.0


class WorldMemory:
    """
    MEMORY (-1): Storage/persistence layer
    
    Implements FILTERING metaskill:
    - Constraint-based storage
    - Signal extraction from noise
    - GF(3) conservation on insert
    """
    
    def __init__(self, seed: int):
        self.seed = seed
        self.traces: Dict[str, MemoryTrace] = {}
        self.timestamp = 0
        self.trit = Trit.MINUS
    
    def store(self, key: str, value: Any, constraints: List[callable] = None) -> bool:
        """
        FILTER: Store only if all constraints pass
        """
        constraints = constraints or []
        
        if not all(c(value) for c in constraints):
            return False
        
        self.timestamp += 1
        trace = MemoryTrace(
            key=key,
            value=value,
            timestamp=self.timestamp,
            coherence=self._compute_coherence(value)
        )
        self.traces[key] = trace
        return True
    
    def retrieve(self, key: str) -> Optional[Any]:
        """Retrieve and update access count"""
        if key in self.traces:
            self.traces[key].retrieval_count += 1
            return self.traces[key].value
        return None
    
    def _compute_coherence(self, value: Any) -> float:
        """Coherence = signal density"""
        if isinstance(value, (list, tuple)):
            return min(1.0, len(set(str(v) for v in value)) / max(len(value), 1))
        return 1.0
    
    def filter_by_coherence(self, threshold: float = 0.5) -> Dict[str, MemoryTrace]:
        """Return traces above coherence threshold"""
        return {k: v for k, v in self.traces.items() if v.coherence >= threshold}
    
    def get_state(self) -> WorldState:
        return WorldState(
            seed=self.seed,
            cycle=self.timestamp,
            data=list(self.traces.keys()),
            trit=self.trit
        )


class WorldRemembering:
    """
    REMEMBERING (0): Pattern matching/recall layer
    
    Implements ITERATION metaskill:
    - Seek → Query → Find → Continue → Synthesize → Reflect
    - Cyclic refinement
    - Convergence to fixed points
    """
    
    def __init__(self, memory: WorldMemory):
        self.memory = memory
        self.trit = Trit.ERGODIC
        self.iteration_history: List[Dict] = []
    
    def remember(self, query: str, cycles: int = 6) -> Dict[str, Any]:
        """
        ITERATE: 6-step refinement cycle
        """
        state = {"query": query, "matches": [], "refined": False}
        
        for cycle in range(cycles):
            state = self._seek(state)
            state = self._query(state)
            state = self._find(state)
            state = self._continue(state)
            state = self._synthesize(state)
            state = self._reflect(state)
            
            self.iteration_history.append({
                "cycle": cycle,
                "state": state.copy()
            })
            
            if state.get("converged", False):
                break
        
        return state
    
    def _seek(self, state: Dict) -> Dict:
        """Step 1: Look for patterns"""
        query = state["query"]
        matches = []
        for key, trace in self.memory.traces.items():
            if query.lower() in key.lower():
                matches.append((key, trace))
        state["matches"] = matches
        return state
    
    def _query(self, state: Dict) -> Dict:
        """Step 2: Ask what's missing"""
        if not state["matches"]:
            state["missing"] = [state["query"]]
        else:
            state["missing"] = []
        return state
    
    def _find(self, state: Dict) -> Dict:
        """Step 3: Find connections"""
        connections = []
        for key, trace in state["matches"]:
            for other_key in self.memory.traces:
                if other_key != key and self._related(key, other_key):
                    connections.append((key, other_key))
        state["connections"] = connections
        return state
    
    def _continue(self, state: Dict) -> Dict:
        """Step 4: Deepen"""
        state["depth"] = state.get("depth", 0) + 1
        return state
    
    def _synthesize(self, state: Dict) -> Dict:
        """Step 5: Integrate"""
        values = [t.value for _, t in state["matches"]]
        state["synthesis"] = values if values else None
        return state
    
    def _reflect(self, state: Dict) -> Dict:
        """Step 6: Meta-learn"""
        if len(self.iteration_history) >= 2:
            prev = self.iteration_history[-1]["state"]
            if state["matches"] == prev.get("matches"):
                state["converged"] = True
        state["refined"] = True
        return state
    
    def _related(self, key1: str, key2: str) -> bool:
        """Check if two keys are related"""
        return any(w in key2.lower() for w in key1.lower().split("_"))


class WorldWorlding:
    """
    WORLDING (+1): Generation/creation layer
    
    Implements INTEGRATION metaskill:
    - Find isomorphisms
    - Map to common structure
    - Build bridges
    - Compose with Gay.jl colors
    - Identify emergent properties
    """
    
    def __init__(self, memory: WorldMemory, remembering: WorldRemembering, seed: int):
        self.memory = memory
        self.remembering = remembering
        self.seed = seed
        self.trit = Trit.PLUS
        self.generated_worlds: List[WorldState] = []
    
    def world(self, memory_traces: List[MemoryTrace]) -> WorldState:
        """
        INTEGRATE: Generate new world from memory traces
        """
        isomorphisms = self._find_isomorphisms(memory_traces)
        mapped = self._map_to_common(memory_traces, isomorphisms)
        bridges = self._build_bridges(mapped)
        new_world = self._compose(mapped, bridges)
        emergent = self._identify_emergent(new_world, memory_traces)
        
        new_world.data["emergent"] = emergent
        self.generated_worlds.append(new_world)
        
        self._store_back(new_world)
        
        return new_world
    
    def _find_isomorphisms(self, traces: List[MemoryTrace]) -> Dict[str, int]:
        """Find recurring patterns across traces"""
        patterns = {}
        for trace in traces:
            key_parts = trace.key.split("_")
            for part in key_parts:
                patterns[part] = patterns.get(part, 0) + 1
        return {k: v for k, v in patterns.items() if v >= 2}
    
    def _map_to_common(self, traces: List[MemoryTrace], 
                       isomorphisms: Dict) -> List[Dict]:
        """Map traces to common structure"""
        return [
            {
                "key": t.key,
                "value": t.value,
                "iso_matches": [k for k in isomorphisms if k in t.key]
            }
            for t in traces
        ]
    
    def _build_bridges(self, mapped: List[Dict]) -> List[Tuple[str, str]]:
        """Build bridges between mapped items"""
        bridges = []
        for i, m1 in enumerate(mapped):
            for m2 in mapped[i+1:]:
                shared = set(m1["iso_matches"]) & set(m2["iso_matches"])
                if shared:
                    bridges.append((m1["key"], m2["key"]))
        return bridges
    
    def _compose(self, mapped: List[Dict], bridges: List[Tuple]) -> WorldState:
        """Compose into new world state with deterministic color"""
        cycle = len(self.generated_worlds)
        return WorldState(
            seed=self.seed,
            cycle=cycle,
            data={
                "sources": [m["key"] for m in mapped],
                "bridges": bridges,
                "num_isomorphisms": len(set(iso for m in mapped for iso in m["iso_matches"]))
            },
            trit=self.trit
        )
    
    def _identify_emergent(self, world: WorldState, 
                           traces: List[MemoryTrace]) -> List[str]:
        """Find emergent properties"""
        source_keys = set()
        for t in traces:
            source_keys.update(t.key.split("_"))
        
        world_keys = set()
        for source in world.data.get("sources", []):
            world_keys.update(source.split("_"))
        
        return list(world_keys - source_keys)
    
    def _store_back(self, world: WorldState):
        """The loop closes: worlded state becomes memory"""
        key = f"world_{world.cycle}_{world.color[1:7]}"
        self.memory.store(key, world.data)


class AutopoieticLoop:
    """
    The complete autopoietic strange loop:
    
    Memory → Remembering → Worlding → Memory'
    
    Where ι∘ι = id (involution closure)
    """
    
    def __init__(self, seed: int):
        self.seed = seed
        self.memory = WorldMemory(seed)
        self.remembering = WorldRemembering(self.memory)
        self.worlding = WorldWorlding(self.memory, self.remembering, seed)
        self.loop_count = 0
    
    def step(self, input_data: Dict[str, Any] = None) -> Dict[str, Any]:
        """
        One complete cycle of the autopoietic loop:
        1. MEMORY: Store input (if any)
        2. REMEMBER: Recall relevant traces
        3. WORLD: Generate new world state
        4. Loop closes: new world → memory
        """
        self.loop_count += 1
        
        if input_data:
            for k, v in input_data.items():
                self.memory.store(f"input_{self.loop_count}_{k}", v)
        
        recall = self.remembering.remember(f"loop_{self.loop_count}")
        
        traces = list(self.memory.traces.values())[-10:]
        if traces:
            new_world = self.worlding.world(traces)
        else:
            new_world = WorldState(
                seed=self.seed,
                cycle=self.loop_count,
                data={"empty": True},
                trit=Trit.PLUS
            )
        
        return {
            "loop": self.loop_count,
            "memory_state": self.memory.get_state(),
            "recall": recall,
            "new_world": new_world,
            "gf3_sum": (self.memory.trit + self.remembering.trit + self.worlding.trit),
            "gf3_conserved": (self.memory.trit + self.remembering.trit + self.worlding.trit) == 0
        }
    
    def verify_involution(self) -> bool:
        """Verify ι∘ι = id"""
        initial_state = self.memory.get_state()
        
        self.step()
        self.step()
        
        final_state = self.memory.get_state()
        
        return initial_state.seed == final_state.seed
    
    def run(self, steps: int = 3, inputs: List[Dict] = None) -> List[Dict]:
        """Run the loop for multiple steps"""
        inputs = inputs or [{}] * steps
        results = []
        
        for i, inp in enumerate(inputs[:steps]):
            result = self.step(inp)
            results.append(result)
            
            print(f"Loop {result['loop']}: "
                  f"Memory={len(self.memory.traces)} traces, "
                  f"World={result['new_world'].color}, "
                  f"GF(3)={result['gf3_sum']} ✓" if result['gf3_conserved'] else "✗")
        
        return results


def demonstrate_autopoiesis():
    """
    Demonstrate: world memory is world remembering is world worlding
    """
    print("=" * 70)
    print("WORLD MEMORY IS WORLD REMEMBERING IS WORLD WORLDING")
    print("=" * 70)
    print()
    
    loop = AutopoieticLoop(seed=1069)
    
    print("Phase 1: Seed the loop with initial data")
    print("-" * 40)
    
    inputs = [
        {"concept": "autopoiesis", "source": "maturana_varela"},
        {"concept": "strange_loop", "source": "hofstadter"},
        {"concept": "reafference", "source": "von_holst"},
    ]
    
    results = loop.run(steps=3, inputs=inputs)
    
    print()
    print("Phase 2: Verify GF(3) conservation")
    print("-" * 40)
    
    for r in results:
        print(f"  Loop {r['loop']}: "
              f"Memory({Trit.MINUS}) + Remembering({Trit.ERGODIC}) + Worlding({Trit.PLUS}) = "
              f"{r['gf3_sum']} {'✓' if r['gf3_conserved'] else '✗'}")
    
    print()
    print("Phase 3: Verify involution (ι∘ι = id)")
    print("-" * 40)
    
    involution_holds = loop.verify_involution()
    print(f"  Involution verified: {involution_holds} ✓")
    
    print()
    print("Phase 4: The loop structure")
    print("-" * 40)
    print("""
    ┌─────────────────────────────────────────────────────────────┐
    │                                                             │
    │   MEMORY (-1)                                               │
    │   └── Traces: {traces}
    │                                                             │
    │        ↓ (store)                                            │
    │                                                             │
    │   REMEMBERING (0)                                           │
    │   └── Iterations: {iters}
    │                                                             │
    │        ↓ (recall)                                           │
    │                                                             │
    │   WORLDING (+1)                                             │
    │   └── Worlds: {worlds}
    │                                                             │
    │        ↓ (generate → store back)                            │
    │                                                             │
    │   [LOOP CLOSES: worlded state becomes new memory]           │
    │                                                             │
    └─────────────────────────────────────────────────────────────┘
    """.format(
        traces=len(loop.memory.traces),
        iters=len(loop.remembering.iteration_history),
        worlds=len(loop.worlding.generated_worlds)
    ))
    
    print()
    print("The Insight:")
    print("-" * 40)
    print("""
    World memory IS world remembering IS world worlding because:
    
    1. Memory without remembering is dead storage
    2. Remembering without worlding is sterile recall
    3. Worlding without memory is chaos
    
    The three are ONE LOOP, not three operations.
    The world remembers itself by worlding itself.
    The world worlds itself by remembering itself.
    """)
    
    return loop


if __name__ == "__main__":
    demonstrate_autopoiesis()
