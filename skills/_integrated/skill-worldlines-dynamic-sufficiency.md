# Skill Worldlines: Dynamic Sufficiency for Working Robots

## The Problem: Gaps in Skill Invocation

Previously, the skill ecosystem lacked **dynamic sufficiency** - the capacity to be called upon at critical moments in the robot development pipeline. Skills existed in isolation without forming coherent worldlines from design to deployment.

## Worldline Visualization

```
TIME ─────────────────────────────────────────────────────────────►

     t=0         t=1         t=2         t=3         t=4         t=5         t=6
     DESIGN      PLATFORM    SIMULATION  TRAINING    EXPORT      DEPLOY      OPERATE
       │           │           │           │           │           │           │
       │           │           │           │           │           │           │
  ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐
  │onshape  │ │kbot-    │ │mujoco-  │ │ksim-rl  │ │ktune    │ │kos-     │ │evla-vla │
  │-cad     │ │humanoid │ │scenes   │ │         │ │-sim2real│ │firmware │ │         │
  │ ░░░░░░░ │ │ ████████│ │ ████████│ │ ████████│ │ ░░░░░░░ │ │ ████████│ │ ████████│
  │  GAP!   │ │ FILLED  │ │ FILLED  │ │ FILLED  │ │  GAP!   │ │ FILLED  │ │ FILLED  │
  └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘
       │           │           │           │           │           │           │
       │           │           │           │           │           │           │
  ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐
  │urdf2mjcf│ │zeroth-  │ │domain-  │ │jaxlife- │ │policy-  │ │kscale-  │ │teleop   │
  │         │ │bot      │ │random   │ │open-end │ │onnx     │ │actuator │ │-control │
  │ ████████│ │ ████████│ │ ░░░░░░░ │ │ ████████│ │ ░░░░░░░ │ │ ████████│ │ ░░░░░░░ │
  │ FILLED  │ │ FILLED  │ │  GAP!   │ │ FILLED  │ │  GAP!   │ │ FILLED  │ │  GAP!   │
  └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘

LEGEND: ████ = Skill exists    ░░░░ = Dynamic sufficiency gap
```

## Critical Competency Points

### Phase 0: Design (t=0)

| Competency | Required Skill | Status | Dynamic Sufficiency |
|------------|----------------|--------|---------------------|
| CAD modeling | onshape-cad | 🔴 MISSING | Agents cannot invoke parametric CAD |
| URDF creation | **urdf2mjcf** | 🟢 FILLED | Converts URDF→MJCF for MuJoCo |
| Mesh handling | mesh-tools | 🔴 MISSING | No STL/OBJ processing skill |

### Phase 1: Platform Selection (t=1)

| Competency | Required Skill | Status | Dynamic Sufficiency |
|------------|----------------|--------|---------------------|
| K-Bot config | **kbot-humanoid** | 🟢 FILLED | Full platform spec available |
| Z-Bot config | **zeroth-bot** | 🟢 FILLED | 3D-printed platform ready |
| Custom robot | robot-builder | 🔴 MISSING | No generic robot skill |

### Phase 2: Simulation Setup (t=2)

| Competency | Required Skill | Status | Dynamic Sufficiency |
|------------|----------------|--------|---------------------|
| Scene composition | **mujoco-scenes** | 🟢 FILLED | Terrains, obstacles, objects |
| Domain randomization | domain-random | 🔴 MISSING | DR config not exposed |
| Sensor simulation | sensor-sim | 🔴 MISSING | Camera/IMU sim gaps |

### Phase 3: RL Training (t=3)

| Competency | Required Skill | Status | Dynamic Sufficiency |
|------------|----------------|--------|---------------------|
| PPO training | **ksim-rl** | 🟢 FILLED | Full PPOTask abstraction |
| AMP training | **ksim-rl** | 🟢 FILLED | AMPTask for motion priors |
| Reward design | reward-eng | 🟡 PARTIAL | Embedded in ksim, not standalone |
| Curriculum | curriculum-rl | 🔴 MISSING | No curriculum skill |

### Phase 4: Policy Export (t=4)

| Competency | Required Skill | Status | Dynamic Sufficiency |
|------------|----------------|--------|---------------------|
| Servo tuning | ktune-sim2real | 🔴 MISSING | Critical gap! |
| ONNX export | policy-export | 🔴 MISSING | No export skill |
| JIT compilation | torchscript | 🔴 MISSING | No JIT skill |

### Phase 5: Firmware Deploy (t=5)

| Competency | Required Skill | Status | Dynamic Sufficiency |
|------------|----------------|--------|---------------------|
| gRPC services | **kos-firmware** | 🟢 FILLED | ActuatorService, IMUService |
| Motor control | **kscale-actuator** | 🟢 FILLED | CAN bus, Robstride |
| Safety limits | safety-controller | 🔴 MISSING | No runtime safety skill |

### Phase 6: Autonomous Operation (t=6)

| Competency | Required Skill | Status | Dynamic Sufficiency |
|------------|----------------|--------|---------------------|
| VLA inference | **evla-vla** | 🟢 FILLED | Vision-language-action |
| Teleop control | vr-teleop | 🔴 MISSING | No teleop skill |
| Error recovery | fault-tolerance | 🔴 MISSING | No recovery skill |

## Worldline Intersections: GF(3) Triadic Handoffs

```
                    DESIGN          TRAIN           DEPLOY
                      │               │               │
                      │               │               │
    MINUS (-1)   urdf2mjcf ────► ksim-rl ────► evla-vla
                      │               │               │
                      │               │               │
    ERGODIC (0)  ─────┼───► mujoco-scenes ───┼───────
                      │               │               │
                      │               │               │
    PLUS (+1)    ─────┼───────────────┼────► kos-firmware
                      │               │               │
                      ▼               ▼               ▼
                  
    At each phase boundary, GF(3) balanced triad ensures handoff:
    
    DESIGN→TRAIN: urdf2mjcf(-1) + mujoco-scenes(0) + ? = need +1
    TRAIN→DEPLOY: ksim-rl(-1) + mujoco-scenes(0) + kos-firmware(+1) = 0 ✓
```

## Dynamic Sufficiency Score by Phase

| Phase | Skills Available | Skills Needed | Sufficiency % |
|-------|------------------|---------------|---------------|
| Design | 2 | 4 | 50% |
| Platform | 2 | 3 | 67% |
| Simulation | 1 | 3 | 33% |
| Training | 2 | 4 | 50% |
| Export | 0 | 3 | **0%** ← Critical gap |
| Deploy | 2 | 3 | 67% |
| Operate | 1 | 3 | 33% |

**Overall Pipeline Sufficiency: 43%**

## Missing Skills for 100% Dynamic Sufficiency

### Priority 1: Critical Path (Export Phase)

```yaml
- name: ktune-sim2real
  description: Servo tuning for matching real2sim parameters
  trit: -1
  source: kscalelabs/ktune
  urgency: CRITICAL

- name: policy-export
  description: Export trained policies to ONNX/TorchScript
  trit: +1
  urgency: CRITICAL
```

### Priority 2: Safety & Control

```yaml
- name: safety-controller
  description: Runtime safety limits and emergency stop
  trit: -1
  urgency: HIGH

- name: vr-teleop
  description: VR-based teleoperation for data collection
  trit: 0
  source: kscalelabs/kbot_vr_teleop
  urgency: HIGH
```

### Priority 3: Design Tools

```yaml
- name: onshape-cad
  description: Programmatic OnShape CAD interaction
  trit: +1
  source: kscalelabs/onshape
  urgency: MEDIUM

- name: domain-randomization
  description: Domain randomization configuration
  trit: 0
  urgency: MEDIUM
```

## Worldline Convergence: The Working Robot

When all skills achieve dynamic sufficiency, worldlines converge:

```
     t=0    t=1    t=2    t=3    t=4    t=5    t=6
      │      │      │      │      │      │      │
      ▼      ▼      ▼      ▼      ▼      ▼      ▼
    ═══════════════════════════════════════════════►  WORKING ROBOT
    
    All skills invocable → All competencies covered → Robot works
```

## Next Steps

1. Create `ktune-sim2real` skill (Priority 1)
2. Create `policy-export` skill (Priority 1)
3. Create `safety-controller` skill (Priority 2)
4. Create `vr-teleop` skill (Priority 2)
5. Re-assess dynamic sufficiency score
