# K-Scale Neighbor Skills: Full Connectivity Map

**Date**: 2026-01-19
**Framework**: GF(3) Neighborhood Awareness, Harmonic Centrality
**Trit**: 0 (ERGODIC - coordinator hub)

---

## Immediate Neighbors (Direct Morphisms)

### Tier 1: K-Scale Ecosystem Triad

| Skill | Trit | Role | Interface | Morphism |
|-------|------|------|-----------|----------|
| **kos-firmware** | 0 | Coordinator | Robot OS | `kos.actuator_control()` |
| **ksim-rl** | +1 | Generator | RL training | `sim.train_policy()` |
| **kinfer-runtime** | -1 | Validator | Model deploy | `kinfer.verify_onnx()` |

**GF(3) Check**: (0) + (+1) + (-1) = 0 ✓

### Tier 2: Sim2Real Transfer Triad

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **entropy-sim2real** | +1 | Generator | Domain randomization |
| **mujoco-scenes** | 0 | Coordinator | Scene definition |
| **urdf2mjcf** | -1 | Validator | Model conversion |

**GF(3) Check**: (+1) + (0) + (-1) = 0 ✓

---

## Active Inference Neighbors

### active-inference-robotics (+1)

**Morphism**: Predictive coding → Motor control
```python
# Active inference policy → K-Scale actuator command
belief_state = agent.infer_state(observation)
action = agent.select_action(belief_state, preferences)
kos.send_command(action)
```

### entropy-sim2real (+1)

**Morphism**: Maximum entropy RL → Robust transfer
```python
# MaxEnt policy → Domain-invariant controller
policy = train_maxent_sac(env, entropy_coef=0.2)
domain_randomizer.apply(env, policy)
```

### langevin-dynamics (-1)

**Morphism**: Stochastic dynamics → Exploration noise
```python
# Langevin noise for exploration
dX = f(X)dt + σ*dW  # σ from K-Scale sensor noise model
```

---

## Dynamical Systems Neighbors

### waddington-landscape (+1)

**Interface**: Potential landscape → Policy attractor basins
```python
# Robot behavior modes as attractor basins
landscape = compute_landscape(policy_space)
stable_gaits = find_attractors(landscape)
```

### attractor (0)

**Interface**: Invariant set → Stable locomotion patterns
```python
# Gait cycle = limit cycle attractor
gait_attractor = identify_limit_cycle(joint_trajectories)
```

### lyapunov-stability (-1)

**Interface**: Stability proof → Controller verification
```python
# Verify controller stability before deployment
V, dV = compute_lyapunov(controller, state_space)
assert dV < 0, "Unstable controller"
```

---

## Hardware Neighbors

### kbot-humanoid (0)

**Interface**: Hardware specs → Simulation parameters
```yaml
# K-Bot MJCF ← Hardware measurements
kbot:
  height: 1.2m
  mass: 45kg
  dof: 21
  actuators: quasi-direct-drive
```

### zeroth-bot (+1)

**Interface**: Entry platform → Transfer learning
```python
# Train on Zeroth, transfer to K-Bot
policy_zeroth = train(zeroth_env)
policy_kbot = finetune(policy_zeroth, kbot_env)
```

### quackbot-duckoid (-1)

**Interface**: Biped research → Stability validation
```python
# Duckling gait → Humanoid locomotion principles
analyze_cog_trajectory(quackbot_walk)
```

---

## Verification Neighbors

### dynamic-sufficiency (+1)

**Interface**: ε-machine gate → Action permissions
```python
# Gate deployment by sufficiency check
if dynamic_sufficiency.check(model, test_coverage):
    kinfer.deploy(model)
else:
    raise InsufficientTestingError
```

### gf3-tripartite (-1)

**Interface**: Trit balance → System health
```python
# Monitor GF(3) across sensor/compute/actuator
health = gf3_check(sensors=-1, compute=0, actuators=+1)
assert health.sum % 3 == 0
```

### narya-proofs (0)

**Interface**: Formal spec → Safety certificate
```
# Narya type for safe robot operation
Safe : Robot → Prop
safe_op : (r : Robot) → Collision-Free r → Safe r
```

---

## Data Neighbors

### duckdb-ies (+1)

**Interface**: Telemetry storage → Analysis
```sql
-- Robot telemetry in DuckDB
SELECT joint, position, velocity, torque
FROM robot_telemetry
WHERE timestamp > now() - INTERVAL '1 hour'
```

### acsets-hatchery (0)

**Interface**: Schema → Robot state graph
```julia
@acset RobotState begin
  Joint := [:hip, :knee, :ankle]
  Sensor := [:imu, :encoder, :force]
  Link := [(hip, knee), (knee, ankle)]
end
```

### gay-mcp (-1)

**Interface**: Color → Robot state visualization
```python
# Deterministic color for robot mode
color = gay.color_at(robot.state_id, seed=1069)
visualize_robot(robot, color=color['hex'])
```

---

## Skill Triads Using K-Scale

### Active Triads

| Triplet | Skills | Status | Purpose |
|---------|--------|--------|---------|
| **#1** | kos-firmware ⊗ kscale ⊗ ksim-rl | ✅ Complete | Core robotics |
| **#2** | entropy-sim2real ⊗ mujoco-scenes ⊗ urdf2mjcf | ✅ Complete | Sim2real |
| **#3** | active-inference-robotics ⊗ kscale ⊗ langevin-dynamics | In Dev | Predictive control |

### Proposed Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Safety | lyapunov-stability ⊗ kscale ⊗ dynamic-sufficiency | Verified deployment |
| Learning | waddington-landscape ⊗ kscale ⊗ attractor | Policy landscape |
| Hardware | zeroth-bot ⊗ kscale ⊗ kbot-humanoid | Transfer chain |

---

## Harmonic Centrality in Skill Graph

```
CORE HUB (0): kscale — connects simulation, hardware, learning
    ↑
GENERATORS (+1): ksim-rl, entropy-sim2real, active-inference-robotics
    ↓
VALIDATORS (-1): kinfer-runtime, urdf2mjcf, lyapunov-stability
```

**Centrality score**: High (orchestrator across K-Scale ecosystem)

---

## Neighbor Loading Pattern

```python
# Load kscale with neighbor awareness
from kscale import KScale

# Tier 1: Always loaded (ecosystem core)
NEIGHBORS_CORE = ['kos-firmware', 'ksim-rl', 'kinfer-runtime']

# Tier 2: Sim2real (load for training)
NEIGHBORS_SIM2REAL = ['entropy-sim2real', 'mujoco-scenes', 'urdf2mjcf']

# Tier 3: Verification (load for deployment)
NEIGHBORS_VERIFY = ['dynamic-sufficiency', 'lyapunov-stability', 'narya-proofs']
```
