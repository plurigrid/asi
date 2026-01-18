# Sim2Real as Predictive Coding (Second-Order Skill)

> *"Zero-shot transfer is successful prediction of future observations in a new domain."*

## Trigger Conditions

- User asks about sim2real transfer mechanisms
- Questions about domain randomization as uncertainty modeling
- Connecting simulation fidelity to predictive accuracy
- Why some policies transfer and others don't
- The role of observation noise in robust deployment

## Overview

**Second-order skill** interpreting sim2real transfer through the lens of active inference and predictive coding. Bridges:

1. **MuJoCo Playground** (DeepMind's sim2real framework)
2. **K-Scale ksim** (JAX-based humanoid training)
3. **Active Inference** (Kenny/Parr/Friston formulation)

## The Predictive Coding Interpretation

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  SIM2REAL AS PREDICTIVE DISTRIBUTION TRANSFER                                │
│                                                                              │
│  In Simulation:                                                              │
│  ══════════════                                                              │
│  Agent learns Q(O_{future} | O_{past}, π) ≈ P_sim(O | S, A)                 │
│                                                                              │
│  The policy π implicitly encodes a predictive model of:                      │
│    - What observations will follow actions                                   │
│    - How the world responds to motor commands                                │
│    - Proprioceptive consequences of movement                                 │
│                                                                              │
│  At Transfer:                                                                │
│  ════════════                                                                │
│  Success ⟺ P_real(O | S, A) ≈ P_sim(O | S, A)                               │
│                                                                              │
│  The policy's predictions about sensory consequences                         │
│  must match reality closely enough for reflexive execution                   │
│                                                                              │
│  Domain Randomization:                                                       │
│  ════════════════════                                                        │
│  Trains Q to be robust over distribution of P_sim                           │
│  Hope: P_real ∈ support(P_sim_randomized)                                   │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Why Zero-Shot Transfer Works (When It Does)

### Kenny's Framework Applied

```python
# In simulation, agent minimizes Perception/Action Divergence:
PAD_sim = VFE(O_past) + KL(Q_future || P_sim)

# At deployment, the implicit assumption is:
PAD_real ≈ VFE(O_past) + KL(Q_future || P_real)

# Zero-shot succeeds when:
KL(P_real || P_sim) < ε  # Sim approximates real well enough

# Domain randomization expands P_sim to cover P_real:
P_sim_randomized = ∫ P_sim(θ) p(θ) dθ
# where θ ~ domain_randomization_distribution
```

### The Entropy Regularizer's Role

```python
# Kenny: PAD differs from EFE by entropy regularizer
# This prevents overconfident predictions!

# In sim2real context:
# - High entropy Q → policy doesn't overfit to sim specifics
# - Robust to observation noise, latency, model mismatch
# - Maps directly to entropy bonus in PPO

# ksim default entropy coefficient:
entropy_coef = 0.01  # Prevents policy collapse, aids transfer
```

## MuJoCo Playground's Approach

From [playground.mujoco.org](https://playground.mujoco.org/):

```
Key Design Decisions for Sim2Real:
═══════════════════════════════════

1. Observation Noise Injection
   - Gaussian noise on proprioception
   - Simulates sensor imperfection
   - Forces policy to be uncertainty-aware

2. Action Latency Modeling  
   - Ring buffer for delayed actions
   - Matches real actuator response time
   - Critical for dynamic movements

3. Domain Randomization
   - Mass, friction, damping variations
   - Trains over distribution of physics
   - P_real should be in support

4. Curriculum Learning
   - Gradual increase in difficulty
   - Matches biological motor learning
   - Prevents local minima
```

## Behavior Type Mapping

| Predictive Coding | Sim2Real | ksim Implementation |
|-------------------|----------|---------------------|
| Generative model P | Simulator | `PhysicsEngine` |
| Recognition model Q | Policy | `Actor + Critic` |
| Prediction error | Reward signal | `Reward.get_reward()` |
| Precision weighting | Reward scaling | `curriculum.Scale` |
| Hierarchical predictions | Multi-level control | Stacked policies |

## The Stateful Observation Pattern

```python
# ksim's StatefulObservation implements predictive memory:
class DelayedJointPositionObservation(StatefulObservation):
    """
    Ring buffer = implicit prediction of recent past.
    Agent must infer current state from delayed observations.
    This is EXACTLY the active inference setup!
    """
    def observe_stateful(self, state: PhysicsState, carry: Array):
        # Carry = memory of recent observations
        # New observation enters buffer
        new_carry = jnp.roll(carry, 1, axis=0)
        new_carry = new_carry.at[0].set(state.data.qpos[7:])
        # Return delayed observation (simulating latency)
        return carry[-1], new_carry
```

## GF(3) Trit Assignment

```
Trit: +1 (PLUS)
Role: Generation (predictive transfer synthesis)
Color: #A1BE3C
URI: skill://sim2real-predictive-coding#A1BE3C

Balanced quad:
  sim2real-predictive-coding (+1) ⊗ 
  active-inference-robotics (+1) ⊗ 
  kscale-kos (-1) ⊗ 
  kscale-kinfer (-1) = 0 ✓

Both second-order skills are generative (+1), balanced by
verification skills that validate on real hardware (-1).
```

## Practical Implications

### 1. When Transfer Fails

```
Transfer failure modes (predictive coding interpretation):

1. OBSERVATION MISMATCH
   - Sim observations ≠ real observations
   - Fix: Better sensor modeling, noise injection

2. DYNAMICS MISMATCH  
   - P_real(s'|s,a) ≠ P_sim(s'|s,a)
   - Fix: System identification, domain randomization

3. OVERCONFIDENT PREDICTIONS
   - Policy too certain about sim-specific patterns
   - Fix: Entropy regularization, dropout, ensembles

4. TEMPORAL MISMATCH
   - Control frequency, latency differences
   - Fix: Latency modeling, action interpolation
```

### 2. Debugging with PAD

```python
def diagnose_transfer_failure(
    policy: Policy,
    sim_env: Environment,
    real_data: Trajectory
) -> Diagnosis:
    """
    Use Kenny's PAD decomposition to find failure mode.
    """
    # Compute VFE on real observations
    vfe_real = policy.variational_free_energy(real_data.observations)
    
    # Compute KL of policy's predictions vs real outcomes
    predicted = policy.predict_trajectory(real_data.observations[:t])
    kl_future = kl_divergence(predicted, real_data.observations[t:])
    
    if vfe_real > threshold:
        return "OBSERVATION_ENCODING_FAILURE"
    elif kl_future > threshold:
        return "PREDICTION_FAILURE"
    else:
        return "LIKELY_ACTION_EXECUTION_FAILURE"
```

## Connections to Other Skills

```yaml
depends_on:
  - active-inference-robotics  # Theoretical foundation
  - kscale-ksim               # Implementation substrate
  - mujoco-playground         # Framework patterns
  - domain-randomization      # Key technique

enables:
  - real-robot-deployment     # Practical application
  - continual-learning        # Online adaptation
  - few-shot-adaptation       # Rapid transfer
```

## Expert Practitioners (2-3-5-7 Sieve)

| Prime | Expert | Contribution |
|-------|--------|--------------|
| 2 | MuJoCo Playground team | Zero-shot framework |
| 3 | Ben Bolte | ksim latency modeling |
| 5 | Pieter Abbeel | Domain randomization pioneer |
| 7 | Josh Tobin | OpenAI sim2real work |

## Narya Compatibility (Structure-Aware Diffing)

| Field | Definition |
|-------|------------|
| `before` | Policy π trained in simulation (weights + predictive distribution) |
| `after` | Policy π deployed on real hardware (same weights, different observations) |
| `delta` | Transfer gap: KL(P_real ∥ P_sim) measured during deployment |
| `birth` | Randomly initialized policy before any training |
| `impact` | 1 if transfer fails (reward < threshold on real), 0 if successful |

### Sim2Real Transfer Event Structure

```python
@dataclass
class Sim2RealNaryaEvent:
    """Structure-aware diff for sim2real transfer validation."""
    event_id: str
    before: SimulationState   # Observation in sim
    after: RealWorldState     # Corresponding observation on hardware
    delta: TransferDelta      # Prediction error between sim and real
    trit: int                 # GF(3): -1=mismatch, 0=within_tolerance, +1=exact_match
    
    @property
    def impact(self) -> int:
        """1 if transfer gap exceeds acceptable threshold."""
        return 1 if self.delta.kl_gap > TRANSFER_THRESHOLD else 0

@dataclass
class TransferDelta:
    kl_gap: float             # KL(P_real || P_sim) for this transition
    observation_error: float  # ||obs_real - obs_sim||
    dynamics_error: float     # ||s'_real - s'_predicted||
    latency_delta: float      # Timing difference (ms)
```

### Domain Randomization as Uncertainty Modeling

```python
def domain_randomization_narya_log(
    policy: Policy,
    sim_envs: list[Environment],  # Randomized ensemble
    real_env: Environment
) -> list[Sim2RealNaryaEvent]:
    """Log transfer events for each domain randomization sample."""
    events = []
    
    for i, sim_env in enumerate(sim_envs):
        # Run same action sequence in sim and real
        sim_traj = rollout(policy, sim_env)
        real_traj = rollout(policy, real_env)
        
        for t, (sim_step, real_step) in enumerate(zip(sim_traj, real_traj)):
            kl_gap = compute_observation_kl(sim_step.obs, real_step.obs)
            
            events.append(Sim2RealNaryaEvent(
                event_id=f"transfer_{i}_{t}",
                before=sim_step,
                after=real_step,
                delta=TransferDelta(
                    kl_gap=kl_gap,
                    observation_error=np.linalg.norm(sim_step.obs - real_step.obs),
                    dynamics_error=np.linalg.norm(sim_step.next_state - real_step.next_state),
                    latency_delta=real_step.timestamp - sim_step.timestamp
                ),
                trit=0 if kl_gap < 0.1 else (-1 if kl_gap > 0.5 else 1)
            ))
    
    return events
```

### Transfer Success Verification

```python
def verify_transfer_success(events: list[Sim2RealNaryaEvent]) -> ProofBundle:
    """Narya-compatible verification of sim2real transfer."""
    return ProofBundle(
        verifiers={
            "observation_consistency": all(e.delta.observation_error < OBS_THRESHOLD for e in events),
            "dynamics_fidelity": all(e.delta.dynamics_error < DYN_THRESHOLD for e in events),
            "latency_bounds": all(e.delta.latency_delta < LAT_THRESHOLD for e in events),
            "gf3_conservation": sum(e.trit for e in events) % 3 == 0
        },
        overall="VERIFIED" if all_pass else "FAILED",
        proof_hash=sha256(json.dumps([e.to_dict() for e in events]))
    )
```

## ACSet Schema

```julia
@present SchSim2RealTransfer(FreeSchema) begin
    # Objects
    SimEnv::Ob
    RealEnv::Ob
    Policy::Ob
    Observation::Ob
    
    # Morphisms
    train::Hom(SimEnv, Policy)
    deploy::Hom(Policy, RealEnv)
    observe_sim::Hom(SimEnv, Observation)
    observe_real::Hom(RealEnv, Observation)
    
    # The transfer morphism (when it exists)
    transfer::Hom(Policy, Policy)  # Identity when successful
    
    # Attributes measuring success
    TransferGap::AttrType
    kl_gap::Attr(Policy, TransferGap)
    
    # Key constraint: transfer succeeds when
    # kl_gap(π) = KL(observe_real ∘ deploy || observe_sim ∘ train) < ε
end
```

## References

- [MuJoCo Playground Technical Report](https://playground.mujoco.org/assets/playground_technical_report.pdf)
- [Kenny (2025) arXiv:2511.20321](https://arxiv.org/abs/2511.20321)
- [Tobin et al. Domain Randomization](https://arxiv.org/abs/1703.06907)
- [K-Scale ksim](https://github.com/kscalelabs/ksim)
