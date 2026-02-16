# K-Scale ksim Skill

> *"RL training library for humanoid locomotion and manipulation. Built on MuJoCo and JAX."*

## Trigger Conditions

- User asks about robot simulation, humanoid locomotion, or RL policy training
- Questions about MuJoCo/MJX, JAX-based physics simulation
- Training walking/manipulation policies for humanoid robots
- Sim2Real transfer, domain randomization, curriculum learning

## Overview

**ksim** is K-Scale Labs' modular reinforcement learning framework for training robot control policies. It provides:

1. **Physics Engines**: MuJoCo (CPU) and MJX (GPU/JAX-native)
2. **Observation System**: Stateless and stateful observations with noise injection
3. **Reward Functions**: Composable, curriculum-scaled reward components
4. **Action Processing**: Latency modeling, actuator dynamics

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│  ksim Control Loop                                                       │
│                                                                          │
│  ┌──────────────┐  step   ┌──────────────┐  observe  ┌──────────────┐   │
│  │ PhysicsState │────────▶│   Trajectory │──────────▶│  Observation │   │
│  │   (MJX/MJ)   │         │   (batched)  │           │   (noisy)    │   │
│  └──────┬───────┘         └──────┬───────┘           └──────────────┘   │
│         │                        │                                       │
│         │ reset                  │ reward                                │
│         ▼                        ▼                                       │
│  ┌──────────────┐         ┌──────────────┐                              │
│  │    Engine    │         │  RewardState │                              │
│  │ (JIT-compiled)│        │  (component) │                              │
│  └──────────────┘         └──────────────┘                              │
│         │                                                                │
│         │ actuate                                                        │
│         ▼                                                                │
│  ┌──────────────┐                                                       │
│  │    Action    │◀─────── policy(observation)                           │
│  │  (latency)   │                                                       │
│  └──────────────┘                                                       │
└─────────────────────────────────────────────────────────────────────────┘
```

## Module Structure

| Module | Purpose | Key Classes |
|--------|---------|-------------|
| `engine.py` | Physics stepping | `MjxEngine`, `MujocoEngine`, `PhysicsEngine` |
| `observation.py` | State extraction | `Observation`, `StatefulObservation` |
| `rewards.py` | Reward computation | `Reward`, `StatefulReward` |
| `actions.py` | Action processing | `Action`, latency buffers |
| `actuators.py` | Motor dynamics | `Actuators`, `PositionActuators` |
| `types.py` | Core dataclasses | `PhysicsState`, `Trajectory`, `RewardState` |
| `curriculum.py` | Training progression | `Scale`, curriculum schedules |
| `terminations.py` | Episode ending | Termination conditions |
| `resets.py` | State initialization | Reset distributions |
| `randomization.py` | Domain randomization | Parameter perturbations |

## Behavior Type Taxonomy

### Tree-Sitter Lifted Type Hierarchy

```
RL_BEHAVIOR_INTERFACE (Root)
├─ SIMULATION_BEHAVIOR
│  ├─ PHYSICS_STEP: dt × Action → State
│  ├─ RESET: InitConfig → State
│  ├─ RENDER: State → Visualization
│  └─ BATCH_VECTORIZATION: 1 Scene → N Scenes (parallel)
│
├─ POLICY_BEHAVIOR  
│  ├─ ACTOR: (Obs, LSTM_Carry) → (Distribution, LSTM_Carry)
│  ├─ CRITIC: (Obs, LSTM_Carry) → (Value, LSTM_Carry)
│  └─ ACTION_SAMPLING: Distribution → Action (JAX random)
│
├─ REWARD_BEHAVIOR
│  ├─ PENALTY_COMPOSITION: [Penalty] → Scalar
│  ├─ JOINT_DEVIATION: Physics → Scalar
│  └─ POSTURE_CONSTRAINT: Physics → Scalar
│
├─ TRAINING_BEHAVIOR
│  ├─ TRAJECTORY_COLLECTION: Action × Physics → Experience
│  ├─ GRADIENT_COMPUTATION: Trajectory → Gradients (PPO)
│  ├─ MODEL_UPDATE: Gradients → Model′
│  └─ CHECKPOINT: Model → Disk
│
├─ CONFIGURATION_BEHAVIOR
│  ├─ HYPERPARAMETER_SPEC: Type-safe declarative
│  └─ ENV_FACTORY: Config → (Model, Physics, Task)
│
└─ RECURRENCE_BEHAVIOR
   ├─ LSTM_STATE_CARRY: Array → LSTM_Carry
   ├─ STATE_RESET: () → LSTM_Carry
   └─ STATE_EVOLUTION: (Carry, Obs) → Carry′
```

### Type Signature Contracts

| Behavior | Input Type | Output Type | JAX/Equinox Traits |
|----------|-----------|------------|-------------------|
| `Actor.forward` | `(Array[B,O], Array[H])` | `(Distribution, Array[H])` | PyTree, JIT-compiled |
| `Critic.forward` | `(Array[B,O], Array[H])` | `(Array[B,1], Array[H])` | PyTree, Differentiable |
| `step(action)` | `Action: Array[B,A]` | `State: PhysicsModel` | Vectorized, MJX batch |
| `get_rewards()` | `PhysicsModel` | `Array[B,1]` | JAX-pure function |
| `sample_action()` | `(Model, PhysicsModel)` | `Action: Array[B,A]` | Random keyed, PRNGKey |
| `Config.__init__()` | Keyword args | `Config: dataclass` | Immutable, type-checked |

### Stateless Behaviors (Pure Functions)

```python
# Observation: PhysicsState → Array
class BasePositionObservation(Observation):
    def observe(self, state: PhysicsState) -> Array:
        return state.data.qpos[0:3]

# Reward: Trajectory → Array  
class BaseHeightReward(Reward):
    def get_reward(self, trajectory: Trajectory) -> Array:
        height = trajectory.qpos[:, 2]
        return jnp.exp(-((height - self.target) ** 2) / (2 * self.scale ** 2))
```

### Stateful Behaviors (With Carry)

```python
# StatefulObservation: (PhysicsState, Carry) → (Array, Carry)
class DelayedJointPositionObservation(StatefulObservation):
    def observe_stateful(self, state, carry):
        # Ring buffer for action latency simulation
        new_carry = jnp.roll(carry, 1, axis=0)
        new_carry = new_carry.at[0].set(state.data.qpos[7:])
        return carry[-1], new_carry

# StatefulReward: (Trajectory, Carry) → (Array, Carry)
class FeetAirTimeReward(StatefulReward):
    def get_reward_stateful(self, trajectory, carry):
        # Track contact state over time
        ...
```

### Neural Network Behavioral Contracts (Equinox)

```python
class Model(eqx.Module):
    actor: Actor   # Stochastic Policy Behavior
    critic: Critic # Value Estimation Behavior

class Actor(eqx.Module):
    """Behavioral Contract: (Obs, LSTM_Carry) → (Distribution, LSTM_Carry)"""
    def forward(self, obs_n: Array, carry: Array) -> tuple[Distribution, Array]:
        ...

class Critic(eqx.Module):
    """Behavioral Contract: (Obs, LSTM_Carry) → (Value, LSTM_Carry)"""
    def forward(self, obs_n: Array, carry: Array) -> tuple[Array, Array]:
        ...
```

## Key Patterns

### 1. JIT Compilation with Equinox

```python
@eqx.filter_jit
def step(self, action, physics_model, physics_state, curriculum_level, rng):
    # Efficient GPU execution via JAX tracing
    ...
```

### 2. Exponential Kernel Rewards

```python
def exp_kernel(x, scale):
    return jnp.exp(-(x ** 2) / (2 * scale ** 2))
```

### 3. Curriculum Scaling

```python
class Scale:
    def __call__(self, curriculum_level: Array) -> Array:
        # Modulate reward/observation based on training progress
        ...
```

## GF(3) Trit Assignment

```
Trit: 0 (ERGODIC)
Role: Infrastructure/Coordination
Color: #25BC3D
URI: skill://kscale-ksim#25BC3D
```

### Balanced Triads

```
kscale-ksim (0) ⊗ kscale-kos (-1) ⊗ gym (+1) = 0 ✓
kscale-ksim (0) ⊗ jax-rl (-1) ⊗ mujoco-playground (+1) = 0 ✓
```

## Related Skills

- `kscale-kos`: K-Scale Operating System (firmware layer)
- `kscale-kinfer`: Model inference engine
- `kscale-urdf`: Robot description conversion
- `gym`: OpenAI Gym environments
- `jax`: JAX numerical computing

## Key Contributors (Cognitive Superposition)

| Contributor | Focus Areas | Commits |
|------------|-------------|---------|
| **codekansas** (Ben Bolte) | Architecture, rewards, training | 1475+ |
| **b-vm** | Randomization, disturbances | 500+ |
| **WT-MM** (Wesley Maa) | Tooling, visualization | 300+ |
| **alik-git** (Ali Kuwajerwala) | Integration, testing | 200+ |

## Commands

```bash
# Install ksim
pip install ksim

# Train a walking policy (RTX 4090: ~30 min for 80 steps)
python -m ksim.train --config configs/kbot_walk.yaml

# Visualize trained policy
python -m ksim.vis --checkpoint path/to/model.ckpt
```

## References

- [kscalelabs/ksim](https://github.com/kscalelabs/ksim) - Main repository
- [kscalelabs/ksim-gym](https://github.com/kscalelabs/ksim-gym) - Training harness
- [MuJoCo Playground](https://arxiv.org/html/2502.08844v1) - Design influences
- [docs.kscale.dev](https://docs.kscale.dev) - Official documentation

## Narya Compatibility (Structure-Aware Diffing)

| Field | Definition |
|-------|------------|
| `before` | `PhysicsState` at timestep t (qpos, qvel, control) |
| `after` | `PhysicsState` at timestep t+1 after action execution |
| `delta` | `Trajectory` segment: the action taken + reward received |
| `birth` | Initial `PhysicsState` from `reset()` with domain randomization |
| `impact` | 1 if episode terminated (fall, out-of-bounds), 0 otherwise |

### Behavior Type Diffing

```python
@dataclass
class KsimNaryaEvent:
    """Structure-aware diff for ksim state transitions."""
    event_id: str
    before: PhysicsState      # State before action
    after: PhysicsState       # State after action
    delta: TrajectorySegment  # Action + reward + info
    trit: int                 # GF(3): -1=penalty, 0=neutral, +1=reward
    
    @property
    def impact(self) -> int:
        """1 if state change is significant (termination/reset)."""
        return 1 if self.delta.done else 0
    
    def to_jsonl(self) -> str:
        return json.dumps({
            "event_id": self.event_id,
            "before_hash": hash_state(self.before),
            "after_hash": hash_state(self.after),
            "delta": {"action": self.delta.action.tolist(),
                      "reward": float(self.delta.reward)},
            "trit": self.trit,
            "impact": self.impact
        })
```

### Replay Determinism

```python
# Same seed → same trajectory (critical for sim2real debugging)
def replay_episode(seed: int, policy: Model) -> list[KsimNaryaEvent]:
    rng = jax.random.PRNGKey(seed)
    state = env.reset(rng)  # birth
    events = []
    
    for t in range(max_steps):
        rng, action_rng = jax.random.split(rng)
        action = policy.sample(state.obs, action_rng)
        
        before = state
        state, reward, done, info = env.step(action)
        
        events.append(KsimNaryaEvent(
            event_id=f"step_{t}",
            before=before,
            after=state,
            delta=TrajectorySegment(action, reward, done, info),
            trit=sign(reward)  # -1, 0, +1
        ))
        
        if done:
            break
    
    return events
```

## ACSet Schema

```julia
@present SchKsim(FreeSchema) begin
    PhysicsState::Ob
    Trajectory::Ob
    Observation::Ob
    Reward::Ob
    Action::Ob
    
    step::Hom(Action, PhysicsState)
    observe::Hom(PhysicsState, Observation)
    reward::Hom(Trajectory, Reward)
    
    StateData::AttrType
    qpos::Attr(PhysicsState, StateData)
    qvel::Attr(PhysicsState, StateData)
end
```
