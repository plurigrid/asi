---
name: multidispatch-rl
description: Multiple dispatch as explicit RL objective - learning optimal method selection across type combinations
metadata:
  skill_type: RL / Type Theory / Dispatch
  interface_ports:
  - Commands
  - Related Skills
trit: 0
color: "#F59E0B"
parents: [julia, open-games, parametrised-optics-cybernetics]
seed: 1729
---

# Multiple Dispatch as Explicit RL Objective

**Status**: Research
**Trit**: 0 (ERGODIC - coordinates dispatch decisions)
**Seed**: 1729 (Hardy-Ramanujan taxicab number)
**Color**: #F59E0B

> *"The dispatcher is the policy. The type signature is the state. The method is the action."*

## Core Insight

**Multiple dispatch IS reinforcement learning:**

| RL Concept | Multiple Dispatch |
|------------|-------------------|
| State s | Type tuple (τ₁, τ₂, ..., τₙ) |
| Action a | Method implementation m |
| Policy π(a\|s) | Dispatch table D |
| Reward r | Utility of method for types |
| Value V(s) | Expected utility of type combination |

## Formal Framework

### State Space: Type Lattice

```
S = T₁ × T₂ × ... × Tₙ

where each Tᵢ is a type lattice with:
  ⊤ = Any (top)
  ⊥ = Union{} (bottom)
  ≤ = subtype relation
```

### Action Space: Method Table

```
A = {m₁, m₂, ..., mₖ}

Each method mⱼ has signature:
  sig(mⱼ) = (τ₁ⱼ, τ₂ⱼ, ..., τₙⱼ)

Method applies when:
  (t₁, t₂, ..., tₙ) ≤ sig(mⱼ)
```

### Policy: Dispatch Function

```julia
# The dispatch policy
π : S → Δ(A)

# Deterministic dispatch (Julia-style)
dispatch(f, args...) =
  argmax_{m ∈ applicable(f, args)} specificity(m)

# Stochastic dispatch (RL exploration)
dispatch_rl(f, args...) =
  sample(softmax(Q(state(args), m) for m in applicable(f, args)))
```

### Reward: Method Utility

```julia
# Reward function
r(s, a) = utility(method=a, types=s)

# Components:
#   - Correctness: does method produce valid output?
#   - Efficiency: runtime/memory cost
#   - Specificity: more specific = higher reward
#   - GF(3): triadic balance bonus
```

## The RL Objective

```
J(π) = 𝔼_{s∼ρ, a∼π(·|s)} [ Σₜ γᵗ r(sₜ, aₜ) ]

Maximize expected discounted utility of dispatch decisions
across the distribution of type combinations encountered.
```

### Bellman Equation for Dispatch

```
Q*(s, a) = r(s, a) + γ Σ_{s'} P(s'|s,a) max_{a'} Q*(s', a')

where:
  s = current type tuple
  a = method selected
  s' = type tuple of return value (for chained dispatch)
  P(s'|s,a) = type transition probability
```

## GF(3) Triadic Dispatch

The trit structure induces a **3-way dispatch hierarchy**:

```
┌─────────────────────────────────────────────────────────────────────┐
│                    GF(3) DISPATCH HIERARCHY                          │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   ┌──────────────┐                                                  │
│   │ PLUS (+1)    │  Generative methods                              │
│   │ Constructors │  create!, generate!, synthesize!                 │
│   └──────┬───────┘                                                  │
│          │                                                          │
│          ▼                                                          │
│   ┌──────────────┐                                                  │
│   │ ERGODIC (0)  │  Coordinative methods                            │
│   │ Transformers │  map, transform, convert                         │
│   └──────┬───────┘                                                  │
│          │                                                          │
│          ▼                                                          │
│   ┌──────────────┐                                                  │
│   │ MINUS (-1)   │  Observational methods                           │
│   │ Observers    │  observe, validate, check                        │
│   └──────────────┘                                                  │
│                                                                      │
│   Dispatch Rule: Σ trits of method sequence ≡ 0 (mod 3)             │
└─────────────────────────────────────────────────────────────────────┘
```

### Triadic Method Signatures

```julia
# Method trit annotation
@trit +1 function generate(x::Input)::Output end
@trit  0 function transform(x::A)::B end
@trit -1 function observe(x::State)::Observation end

# GF(3)-aware dispatch
function dispatch_gf3(f, args...; budget::Trit)
    applicable = methods(f, typeof.(args))

    # Filter by trit budget
    valid = filter(m -> trit(m) == budget, applicable)

    # Select most specific
    isempty(valid) ? nothing : most_specific(valid)
end
```

## RL Training Loop

```python
class DispatchAgent:
    """RL agent that learns optimal dispatch table."""

    def __init__(self, type_lattice, method_table):
        self.Q = {}  # Q-table: (type_tuple, method) → value
        self.type_lattice = type_lattice
        self.method_table = method_table

    def select_method(self, types, epsilon=0.1):
        """ε-greedy method selection."""
        applicable = self.get_applicable(types)

        if random.random() < epsilon:
            # Explore: random applicable method
            return random.choice(applicable)
        else:
            # Exploit: best Q-value
            return max(applicable, key=lambda m: self.Q.get((types, m), 0))

    def update(self, types, method, reward, next_types):
        """Q-learning update."""
        current_q = self.Q.get((types, method), 0)

        # Max Q for next state
        next_applicable = self.get_applicable(next_types)
        max_next_q = max(self.Q.get((next_types, m), 0)
                         for m in next_applicable) if next_applicable else 0

        # Bellman update
        self.Q[(types, method)] = current_q + self.alpha * (
            reward + self.gamma * max_next_q - current_q
        )

    def get_applicable(self, types):
        """Get methods applicable to type tuple."""
        return [m for m in self.method_table
                if self.subtype(types, m.signature)]
```

## Specificity as Reward Shaping

Julia's dispatch uses **specificity** - more specific methods are preferred. This is natural reward shaping:

```julia
# Specificity reward component
function specificity_reward(method, types)
    sig = signature(method)

    # Distance from types to signature in lattice
    distances = [lattice_distance(t, s) for (t, s) in zip(types, sig)]

    # Closer = higher reward
    return -sum(distances)
end

# Full reward
function dispatch_reward(method, types, result)
    correctness = is_valid(result) ? 1.0 : -10.0
    specificity = specificity_reward(method, types)
    efficiency = -log(runtime(method, types))
    gf3_bonus = is_balanced(method) ? 0.5 : 0.0

    return correctness + 0.3*specificity + 0.1*efficiency + gf3_bonus
end
```

## Hierarchical Dispatch (Powers PCT)

```
Level 5 (Program):    Which function to call?
    ↓ dispatches to
Level 4 (Transition): Which method family?
    ↓ dispatches to
Level 3 (Config):     Which specific method?
    ↓ dispatches to
Level 2 (Sensation):  Which argument processing?
    ↓ dispatches to
Level 1 (Intensity):  Which low-level implementation?
```

```julia
struct HierarchicalDispatch
    level5_policy::Policy  # Function selection
    level4_policy::Policy  # Method family
    level3_policy::Policy  # Specific method
    level2_policy::Policy  # Argument handling
    level1_policy::Policy  # Implementation
end

function hierarchical_dispatch(hd::HierarchicalDispatch, call)
    f = hd.level5_policy(call.context)
    family = hd.level4_policy(f, call.arg_types)
    method = hd.level3_policy(family, call.arg_values)
    args = hd.level2_policy(method, call.raw_args)
    impl = hd.level1_policy(method, hardware_context())

    return impl(args...)
end
```

## Narya Type for Dispatch Policy

```narya
-- Dispatch policy as dependent type
def DispatchPolicy : Type := sig (
  types : TypeTuple,
  methods : List Method,

  -- Policy function
  select : (s : types) → (applicable s methods) → Method,

  -- Optimality condition
  optimal : ∀ (s : types) (ms : applicable s methods),
    Q(s, select s ms) ≥ Q(s, m) for all m ∈ ms,

  -- GF(3) conservation
  balanced : ∀ (seq : List (types × Method)),
    (Σ (_, m) ∈ seq, trit m) ≡ 0 (mod 3)
)
```

## Skill Dispatch as RL

Claude Code's skill system IS multiple dispatch:

```
State s = (user_request, context, available_skills)
Action a = skill to invoke
Reward r = task_completion_quality + efficiency + user_satisfaction

Policy π = skill selection function
```

```python
class SkillDispatcher:
    """RL-trained skill selector."""

    def dispatch(self, request, context):
        # State encoding
        state = encode_state(request, context)

        # Get applicable skills
        applicable = [s for s in self.skills
                      if s.matches(request, context)]

        # Policy selection (learned)
        skill = self.policy.select(state, applicable)

        # Execute and observe reward
        result = skill.execute(request, context)
        reward = self.compute_reward(result)

        # Update policy
        self.policy.update(state, skill, reward)

        return result
```

## Open Games Connection

Multiple dispatch is a **compositional game**:

```
                    play (type input)
    Dispatcher ─────────────────────────► Method
         │                                    │
         │                                    │
         └────────────────────────────────────┘
                   coplay (result feedback)
```

```haskell
-- Dispatch as open game
dispatchGame :: OpenGame TypeTuple Method
dispatchGame = OpenGame {
  play = \types -> selectMethod types,
  coplay = \types method result -> updateQ types method (reward result)
}
```

## Implementation: Julia + Flux.jl

```julia
using Flux

# Neural dispatch policy
struct NeuralDispatch
    encoder::Chain      # Type tuple → embedding
    q_network::Chain    # Embedding × method_id → Q-value
    method_embeddings   # Learned method representations
end

function (nd::NeuralDispatch)(types)
    # Encode type tuple
    type_emb = nd.encoder(encode_types(types))

    # Compute Q-values for all methods
    q_values = [nd.q_network(vcat(type_emb, nd.method_embeddings[m]))
                for m in 1:num_methods]

    # Return softmax policy
    softmax(q_values)
end

# Training
function train_dispatch!(nd, experiences)
    for (types, method, reward, next_types) in experiences
        # Bellman target
        next_q = maximum(nd(next_types))
        target = reward + γ * next_q

        # Update
        grads = gradient(Flux.params(nd)) do
            predicted = nd.q_network(vcat(
                nd.encoder(encode_types(types)),
                nd.method_embeddings[method]
            ))
            Flux.mse(predicted, target)
        end
        Flux.update!(opt, Flux.params(nd), grads)
    end
end
```

## GF(3) Triads

```
open-games (-1) ⊗ multidispatch-rl (0) ⊗ julia-dispatch (+1) = 0 ✓
parametrised-optics (-1) ⊗ multidispatch-rl (0) ⊗ powers-pct (+1) = 0 ✓
skill-dispatch (-1) ⊗ multidispatch-rl (0) ⊗ truealife (+1) = 0 ✓
```

## Commands

```bash
# Train dispatch policy on type traces
just dispatch-train traces.json

# Evaluate dispatch decisions
just dispatch-eval --types "(Int, String, Float64)"

# Visualize Q-table
just dispatch-viz

# Export to Julia dispatch table
just dispatch-export julia
```

## Related Skills

| Skill | Connection |
|-------|------------|
| `julia` | Native multiple dispatch |
| `open-games` | Compositional game semantics |
| `parametrised-optics-cybernetics` | ⊛ action selection |
| `truealife` | ALife reward structures |
| `powers-pct` | Hierarchical control |

---

**Skill Name**: multidispatch-rl
**Type**: RL / Type Theory / Dispatch
**Trit**: 0 (ERGODIC - the dispatcher coordinates)
**Key Insight**: Dispatch table = learned policy over type lattice
**Objective**: Maximize expected utility of method selection


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
