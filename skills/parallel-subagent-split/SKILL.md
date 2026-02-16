# Parallel Subagent Split Skill

> Categorical formalism for parallel agent decomposition with GF(3) conservation

**Version**: 1.0.0
**Trit**: +1 (PLUS - generative/splitting)
**Domain**: distributed-systems, category-theory, agent-architecture

---

## Overview

**Parallel Subagent Split** models the decomposition of a single agent into multiple parallel subagents using categorical constructs:

```
                    ┌─────────────┐
                    │   Agent     │
                    │  (unified)  │
                    └──────┬──────┘
                           │ split (+1)
           ┌───────────────┼───────────────┐
           ▼               ▼               ▼
    ┌──────────┐    ┌──────────┐    ┌──────────┐
    │ Agent₁   │    │ Agent₂   │    │ Agent₃   │
    │ trit:-1  │    │ trit:0   │    │ trit:+1  │
    └──────────┘    └──────────┘    └──────────┘
           │               │               │
           └───────────────┼───────────────┘
                           │ join (-1)
                           ▼
                    ┌─────────────┐
                    │   Result    │
                    │ (merged)    │
                    └─────────────┘
```

---

## Three Categorical Models

### 1. Coproduct: Agent₁ + Agent₂ + Agent₃ (Parallel Split)

**Semantics**: Either/Or choice — exactly one agent handles each task.

```
        ι₁          ι₂          ι₃
Agent₁ ───→ Agent₁ + Agent₂ + Agent₃ ←─── Agent₃
                      ↑
                      │ι₂
                   Agent₂

Universal property: For any f₁, f₂, f₃ to X,
∃! [f₁, f₂, f₃]: Agent₁ + Agent₂ + Agent₃ → X
```

```julia
using Catlab.CategoricalAlgebra

@present SchAgentCoproduct(FreeSchema) begin
    Agent₁::Ob; Agent₂::Ob; Agent₃::Ob
    Coproduct::Ob
    
    ι₁::Hom(Agent₁, Coproduct)
    ι₂::Hom(Agent₂, Coproduct)
    ι₃::Hom(Agent₃, Coproduct)
    
    # Attribute for trit assignment
    Trit::AttrType
    trit₁::Attr(Agent₁, Trit)  # -1
    trit₂::Attr(Agent₂, Trit)  # 0
    trit₃::Attr(Agent₃, Trit)  # +1
end
```

**Use Case**: Task routing where only one subagent should handle each request.

---

### 2. Product: Agent₁ × Agent₂ × Agent₃ (Synchronized Join)

**Semantics**: AND combination — all agents must complete before merge.

```
                    Agent₁ × Agent₂ × Agent₃
                     /         |         \
                  π₁          π₂          π₃
                   ↓           ↓           ↓
                Agent₁     Agent₂     Agent₃

Universal property: For any g with maps to all agents,
∃! ⟨g₁, g₂, g₃⟩: X → Agent₁ × Agent₂ × Agent₃
```

```julia
@present SchAgentProduct(FreeSchema) begin
    Agent₁::Ob; Agent₂::Ob; Agent₃::Ob
    Product::Ob
    
    π₁::Hom(Product, Agent₁)
    π₂::Hom(Product, Agent₂)
    π₃::Hom(Product, Agent₃)
    
    # Synchronization barrier
    SyncState::AttrType
    sync::Attr(Product, SyncState)
end
```

**Use Case**: Consensus protocols where all subagents must agree.

---

### 3. Monoidal Tensor: Agent₁ ⊗ Agent₂ ⊗ Agent₃ (Independent Parallel)

**Semantics**: Truly independent execution — no shared context.

```
Agent₁ ⊗ Agent₂ ⊗ Agent₃

Properties:
- Associativity: (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)
- Unit: I ⊗ A ≅ A ≅ A ⊗ I
- Braiding: A ⊗ B ≅ B ⊗ A (symmetric monoidal)
```

```python
from discopy import Ty, Box, Diagram, Functor

# Types for agents
Agent1 = Ty('Agent₁')
Agent2 = Ty('Agent₂')  
Agent3 = Ty('Agent₃')
Result = Ty('Result')

# Tensor product = parallel composition
parallel_agents = Agent1 @ Agent2 @ Agent3

# Task boxes
task1 = Box('task₁', Ty(), Agent1)
task2 = Box('task₂', Ty(), Agent2)
task3 = Box('task₃', Ty(), Agent3)

# Parallel split
split = task1 @ task2 @ task3  # : I → Agent₁ ⊗ Agent₂ ⊗ Agent₃

# Merge box
merge = Box('merge', Agent1 @ Agent2 @ Agent3, Result)

# Full diagram: split >> merge
parallel_computation = split >> merge
```

**Use Case**: Embarrassingly parallel workloads with no inter-agent communication.

---

## DisCoPy String Diagram Representation

```python
"""
parallel_subagent_split.py - DisCoPy string diagrams for agent splitting
"""
from discopy import *
from discopy.monoidal import Ty, Box, Diagram, Id

# === Type Definitions ===
Task = Ty('Task')
Agent = Ty('Agent')
Result = Ty('Result')

# Trit-labeled agent types
AgentMinus = Ty('A₋')   # trit = -1
AgentZero = Ty('A₀')    # trit = 0
AgentPlus = Ty('A₊')    # trit = +1

# === Splitting Operations ===

class Split(Box):
    """Split single task into three parallel agents."""
    def __init__(self):
        super().__init__(
            name='split',
            dom=Task,
            cod=AgentMinus @ AgentZero @ AgentPlus
        )
        self.trit = +1  # Generative operation

class Merge(Box):
    """Merge three agent results into one."""
    def __init__(self):
        super().__init__(
            name='merge',
            dom=AgentMinus @ AgentZero @ AgentPlus,
            cod=Result
        )
        self.trit = -1  # Consumptive operation

class Process(Box):
    """Individual agent processing with trit assignment."""
    def __init__(self, agent_type: Ty, trit: int):
        name = f'proc_{trit:+d}'
        super().__init__(name=name, dom=agent_type, cod=agent_type)
        self.trit = trit

# === GF(3) Conserving Diagram ===

def make_parallel_diagram():
    """
    Construct full parallel computation diagram.
    
    Task → [Split(+1)] → A₋ ⊗ A₀ ⊗ A₊ → [Merge(-1)] → Result
    
    GF(3) balance: +1 (split) + (-1 + 0 + 1) (agents) + (-1) (merge) = 0 ✓
    """
    # Split task into three
    split = Split()
    
    # Parallel processing (tensor product)
    proc_minus = Process(AgentMinus, -1)
    proc_zero = Process(AgentZero, 0)
    proc_plus = Process(AgentPlus, +1)
    parallel = proc_minus @ proc_zero @ proc_plus
    
    # Merge results
    merge = Merge()
    
    # Compose: split >> parallel >> merge
    return split >> parallel >> merge

def verify_gf3(diagram):
    """Verify GF(3) conservation for diagram."""
    total_trit = 0
    for box in diagram.boxes:
        if hasattr(box, 'trit'):
            total_trit += box.trit
    return total_trit % 3 == 0

# === Trace Operation (Feedback Loops) ===

class TracedAgent(Box):
    """Agent with feedback loop via trace."""
    def __init__(self, inner: Box, feedback_type: Ty):
        # Trace: (A ⊗ X → B ⊗ X) ↦ (A → B)
        self.inner = inner
        self.feedback = feedback_type
        super().__init__(
            name=f'Tr({inner.name})',
            dom=inner.dom,
            cod=inner.cod
        )
    
    def trace(self):
        """Compute traced diagram."""
        # Identity on feedback wire + inner computation
        return self.inner  # Simplified; real trace uses cups/caps

def add_feedback_loop(diagram, feedback_state: Ty):
    """
    Add trace for stateful feedback.
    
    Trace turns: A ⊗ S → B ⊗ S  into  A → B
    where S is the state/feedback wire.
    """
    # Cup and cap for feedback
    cup = Box('cup', Ty(), feedback_state @ feedback_state)
    cap = Box('cap', feedback_state @ feedback_state, Ty())
    
    # Construct traced diagram
    # This models iterative refinement across subagent generations
    return TracedAgent(diagram, feedback_state)

# === Drawing ===

def draw_parallel_split():
    """Generate SVG of parallel split diagram."""
    diagram = make_parallel_diagram()
    diagram.draw(
        figsize=(10, 6),
        path='parallel_split.svg',
        fontsize=12
    )
    return diagram

# === Example Usage ===

if __name__ == "__main__":
    # Build diagram
    diagram = make_parallel_diagram()
    
    # Verify GF(3)
    assert verify_gf3(diagram), "GF(3) conservation violated!"
    print("✓ GF(3) conserved")
    
    # Show structure
    print(f"Domain: {diagram.dom}")
    print(f"Codomain: {diagram.cod}")
    print(f"Boxes: {[b.name for b in diagram.boxes]}")
    
    # Draw (if matplotlib available)
    try:
        draw_parallel_split()
        print("✓ Diagram saved to parallel_split.svg")
    except ImportError:
        print("⚠ matplotlib not available for drawing")
```

---

## GF(3) Conservation Across Splits

### Trit Accounting

| Operation | Trit | Role |
|-----------|------|------|
| Split | +1 | Creates new agents (generative) |
| Agent₋ | -1 | Validator/checker role |
| Agent₀ | 0 | Coordinator/neutral |
| Agent₊ | +1 | Generator/creator role |
| Merge | -1 | Consumes agents (destructive) |

### Conservation Law

```
Σ(trits) ≡ 0 (mod 3)

Example:
  split(+1) + agent₋(-1) + agent₀(0) + agent₊(+1) + merge(-1)
= +1 + (-1) + 0 + (+1) + (-1)
= 0 ≡ 0 (mod 3) ✓
```

### SplitMix64 Seed Distribution

```python
def split_seeds(parent_seed: int, n_children: int = 3) -> list:
    """
    Deterministically derive child seeds from parent.
    Each child gets independent but reproducible stream.
    """
    GOLDEN = 0x9E3779B97F4A7C15
    seeds = []
    for i in range(n_children):
        child_seed = (parent_seed + GOLDEN * (i + 1)) & 0xFFFFFFFFFFFFFFFF
        seeds.append(child_seed)
    return seeds

# Trit assignment from seed
def seed_to_trit(seed: int) -> int:
    """Map seed to trit via modular arithmetic."""
    return (seed % 3) - 1  # → -1, 0, or +1
```

---

## Trace Operation for Feedback Loops

### Categorical Trace

In a traced monoidal category, the trace operation models feedback:

```
Tr_X : Hom(A ⊗ X, B ⊗ X) → Hom(A, B)

For agents: Tr_State(f) takes a stateful agent and produces a stateless one
by "looping" the state back.
```

### Implementation

```python
from discopy.ribbon import Ty, Box, Cup, Cap

State = Ty('State')  # Feedback wire

class IterativeAgent(Box):
    """Agent that refines via feedback loop."""
    
    def __init__(self, base_agent: Box, max_iterations: int = 3):
        self.base = base_agent
        self.max_iter = max_iterations
        super().__init__(
            name=f'Iter({base_agent.name})',
            dom=base_agent.dom,
            cod=base_agent.cod
        )
    
    def as_traced_diagram(self):
        """
        Construct traced diagram for iteration.
        
        Uses cup/cap to create feedback loop:
        
             ┌─────────────┐
         A ──┤             ├── B
             │   Agent     │
             │   ┌───┐     │
             │   │   │ S   │
             └───┴───┴─────┘
                 └───┘ (trace)
        """
        # Augment with state wire
        augmented = self.base  # base: A → B
        
        # Create feedback via cap-cup
        # cap: () → S ⊗ S
        # cup: S ⊗ S → ()
        
        return augmented  # Simplified
```

### Feedback-Aware GF(3)

```
Trace preserves GF(3):
  If f: A ⊗ S → B ⊗ S has GF(3) = k
  Then Tr_S(f): A → B has GF(3) = k

The feedback wire S contributes 0 net trits (same in, same out).
```

---

## Integration with Bisimulation Game

### Equivalence Checking for Parallel Subagents

```python
from bisimulation_game import BisimulationGame

class ParallelBisimulation:
    """
    Verify that different split strategies produce equivalent results.
    
    System 1: Coproduct split (task routing)
    System 2: Tensor split (independent parallel)
    
    Bisimilar iff no observer can distinguish outcomes.
    """
    
    def __init__(self, seed: int = 1069):
        self.seed = seed
        self.game = BisimulationGame(
            system1=self.coproduct_system,
            system2=self.tensor_system,
            seed=seed
        )
    
    def coproduct_system(self, task):
        """Route task to exactly one agent."""
        agent_id = hash(task) % 3
        return self.agents[agent_id].process(task)
    
    def tensor_system(self, task):
        """Process on all agents, combine results."""
        results = [a.process(task) for a in self.agents]
        return self.merge(results)
    
    def verify_equivalence(self, tasks: list) -> dict:
        """
        Play bisimulation game over task sequence.
        
        Returns verification report with GF(3) accounting.
        """
        log = []
        for task in tasks:
            # Attacker chooses system and makes move
            attacker_move = self.game.attacker_move("s1", task)
            
            # Defender responds
            defender_move = self.game.defender_respond(task)
            
            # Arbiter checks
            conserved = self.game.arbiter_verify()
            
            log.append({
                "task": task,
                "attacker_trit": attacker_move,
                "defender_trit": defender_move,
                "conserved": conserved
            })
        
        return {
            "rounds": len(log),
            "all_matched": all(r["conserved"] for r in log),
            "gf3_total": sum(r["attacker_trit"] + r["defender_trit"] for r in log) % 3,
            "log": log
        }
```

### Bisimulation Diagram

```
╔═══════════════════════════════════════════════════════════════════╗
║           PARALLEL SPLIT BISIMULATION GAME                        ║
╠═══════════════════════════════════════════════════════════════════╣
║                                                                   ║
║  ROUND 1:                                                         ║
║  ┌─ ATTACKER (S₁: Coproduct) ────────────────────────────────────┐║
║  │ Route task T₁ to Agent₂ (trit: 0)                             │║
║  │ Transition: ι₂(T₁) in Agent₁ + Agent₂ + Agent₃                │║
║  └───────────────────────────────────────────────────────────────┘║
║                                                                   ║
║  ┌─ DEFENDER (S₂: Tensor) ───────────────────────────────────────┐║
║  │ Process T₁ on Agent₁ ⊗ Agent₂ ⊗ Agent₃ in parallel           │║
║  │ Merge results to match ι₂ behavior                            │║
║  │ Response: MATCHED ✓                                            ║
║  └───────────────────────────────────────────────────────────────┘║
║                                                                   ║
║  ┌─ ARBITER ─────────────────────────────────────────────────────┐║
║  │ GF(3): (-1) + 0 + (+1) = 0 ✓                                  │║
║  │ Observational equivalence: VERIFIED                           │║
║  └───────────────────────────────────────────────────────────────┘║
║                                                                   ║
╚═══════════════════════════════════════════════════════════════════╝
```

---

## ACSet Schema for Agent Decomposition

```julia
using Catlab.CategoricalAlgebra
using StructuredDecompositions

@present SchParallelAgents(FreeSchema) begin
    # Objects
    Task::Ob
    Agent::Ob
    Result::Ob
    
    # Morphisms
    assigned_to::Hom(Task, Agent)
    produces::Hom(Agent, Result)
    merged_from::Hom(Result, Result)  # For composition
    
    # Attributes
    TritType::AttrType
    SeedType::AttrType
    StateType::AttrType
    
    trit::Attr(Agent, TritType)
    seed::Attr(Agent, SeedType)
    state::Attr(Agent, StateType)
end

@acset_type ParallelAgentGraph(SchParallelAgents, index=[:assigned_to, :produces])

function create_split(parent_seed::UInt64)
    """Create parallel agent graph with GF(3) balanced trits."""
    G = ParallelAgentGraph()
    
    # Create three agents
    child_seeds = split_seeds(parent_seed, 3)
    
    add_part!(G, :Agent, trit=-1, seed=child_seeds[1], state="ready")
    add_part!(G, :Agent, trit=0,  seed=child_seeds[2], state="ready")
    add_part!(G, :Agent, trit=+1, seed=child_seeds[3], state="ready")
    
    # Verify GF(3)
    @assert sum(G[:trit]) % 3 == 0 "GF(3) violated!"
    
    G
end
```

---

## Structured Decomposition for Agent Hierarchies

```julia
using StructuredDecompositions

function decompose_agent_tree(root_task, max_depth::Int)
    """
    Build tree decomposition of agent hierarchy.
    
    Each level splits into 3 subagents.
    Adhesions track shared state between siblings.
    """
    
    # Shape graph: binary tree structure
    shape = StrDecomp.tree_shape(3, max_depth)
    
    # Functor: shape → Category of agent graphs
    function agent_functor(node)
        if is_leaf(node)
            return single_agent_graph(node.seed)
        else
            return split_graph(node.seed, 3)
        end
    end
    
    # Build structured decomposition
    decomp = StrDecomp(shape, agent_functor)
    
    # Verify: sheaf condition ensures consistent merge
    verify_sheaf_condition(decomp)
    
    decomp
end
```

---

## GF(3) Synergistic Triads

```
# Parallel split participates in these balanced triads:

bisimulation-game (-1) ⊗ parallel-subagent-split (0) ⊗ triad-interleave (+1) = 0 ✓
structured-decomp (-1) ⊗ parallel-subagent-split (0) ⊗ cognitive-superposition (+1) = 0 ✓
unworld (-1) ⊗ parallel-subagent-split (0) ⊗ gh-interactome (+1) = 0 ✓
acsets-relational-thinking (-1) ⊗ parallel-subagent-split (0) ⊗ specter-acset (+1) = 0 ✓
```

---

## Commands

```bash
# Create parallel split diagram
just parallel-split-diagram SEED N_AGENTS

# Verify GF(3) conservation
just parallel-split-gf3 SEED

# Run bisimulation equivalence check
just parallel-split-bisim SYSTEM1 SYSTEM2

# Generate ACSet for agent graph
just parallel-split-acset SEED

# Draw DisCoPy string diagram
python parallel_subagent_split.py

# Interleave with triad scheduler
just triad-interleave SEED N_TRIPLETS round_robin
```

---

## Mathematical Summary

| Construct | Category | Universal Property | Use Case |
|-----------|----------|-------------------|----------|
| **Coproduct** A₁ + A₂ + A₃ | Set | Unique [f₁,f₂,f₃] to any target | Task routing |
| **Product** A₁ × A₂ × A₃ | Set | Unique ⟨f₁,f₂,f₃⟩ from any source | Consensus sync |
| **Tensor** A₁ ⊗ A₂ ⊗ A₃ | MonCat | Independent parallel | Embarrassingly parallel |
| **Trace** Tr_X(f) | TracedMonCat | Feedback loop | Iterative refinement |

---

## References

- Patterson et al., "Categorical Data Structures for Technical Computing" (2022)
- Bumpus et al., "Structured Decompositions" arXiv:2207.06091
- Joyal, Street, Verity, "Traced Monoidal Categories" (1996)
- de Felice et al., "DisCoPy: Monoidal Categories in Python" (2020)
- Milner, "Communication and Concurrency" (1989) — bisimulation games

---

**Skill Name**: parallel-subagent-split
**Type**: Distributed Agent Architecture
**Trit**: +1 (PLUS - generative/splitting)
**GF(3)**: Conserved via trit accounting
**Dependencies**: discopy, bisimulation-game, triad-interleave, acsets, structured-decomp
