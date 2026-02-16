---
name: kbot-humanoid
description: K-Bot humanoid robot platform - hardware specs, MJCF models, and deployment configurations. The flagship K-Scale humanoid robot.
version: 1.0.0
category: robotics-platform
author: K-Scale Labs
source: kscalelabs/kbot
license: MIT
trit: -1
trit_label: MINUS
color: "#5B45C2"
verified: false
featured: true
---

# K-Bot Humanoid Skill

**Trit**: -1 (MINUS - specification/verification)
**Color**: #5B45C2 (Purple)
**URI**: skill://kbot-humanoid#5B45C2

## Overview

K-Bot is K-Scale Labs' flagship humanoid robot platform. This skill covers hardware specifications, MJCF model configurations, and deployment workflows.

## Robot Specifications

```
┌────────────────────────────────────────────────────────────────┐
│                      K-BOT HUMANOID                            │
├────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Height: ~1.4m                                                 │
│  Weight: ~30kg                                                 │
│  DOF: 20+ joints                                               │
│                                                                 │
│  Actuators:                                                     │
│  ├── Robstride motors (custom driver)                          │
│  ├── Position/velocity/torque control                          │
│  └── ~40 Nm peak torque per joint                              │
│                                                                 │
│  Sensors:                                                       │
│  ├── IMU (6-axis)                                              │
│  ├── Joint encoders                                            │
│  ├── Cameras (RGB)                                             │
│  └── Force sensors (feet)                                      │
│                                                                 │
│  Compute:                                                       │
│  ├── Onboard: Jetson/custom                                    │
│  └── Inference: Policy runs at 50-100 Hz                       │
│                                                                 │
└────────────────────────────────────────────────────────────────┘
```

## MJCF Model

```xml
<!-- kbot.mjcf excerpt -->
<mujoco model="kbot">
  <compiler angle="radian" meshdir="meshes"/>
  
  <default>
    <joint damping="0.5" armature="0.01"/>
    <geom friction="1 0.005 0.001" condim="3"/>
  </default>
  
  <worldbody>
    <body name="torso" pos="0 0 1.0">
      <freejoint name="root"/>
      <geom type="mesh" mesh="torso"/>
      
      <!-- Legs -->
      <body name="hip_l" pos="0 0.1 0">
        <joint name="hip_yaw_l" type="hinge" axis="0 0 1"/>
        <joint name="hip_roll_l" type="hinge" axis="1 0 0"/>
        <joint name="hip_pitch_l" type="hinge" axis="0 1 0"/>
        <!-- ... -->
      </body>
      
      <!-- Arms -->
      <body name="shoulder_l" pos="0 0.2 0.4">
        <joint name="shoulder_pitch_l" type="hinge" axis="0 1 0"/>
        <joint name="shoulder_roll_l" type="hinge" axis="1 0 0"/>
        <!-- ... -->
      </body>
    </body>
  </worldbody>
  
  <actuator>
    <position name="hip_yaw_l_pos" joint="hip_yaw_l" kp="100"/>
    <position name="hip_roll_l_pos" joint="hip_roll_l" kp="100"/>
    <!-- ... -->
  </actuator>
</mujoco>
```

## Deployment Pipeline

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   KSIM      │───▶│   Policy    │───▶│   KOS       │───▶│   K-Bot     │
│   Training  │    │   Export    │    │   Firmware  │    │   Hardware  │
└─────────────┘    └─────────────┘    └─────────────┘    └─────────────┘
       │                  │                  │                  │
       ▼                  ▼                  ▼                  ▼
   PPO/AMP in        ONNX/JIT           gRPC actuator      Real robot
   MJX sim           conversion         commands            execution
```

## Training with KSIM

```python
from ksim.robots.kbot import KBotConfig
from ksim import PPOTask

class KBotWalking(PPOTask):
    robot = KBotConfig(
        model_path="kbot-headless.mjcf",
        joint_names=KBotConfig.DEFAULT_JOINTS,
        actuator_config={
            "kp": 100.0,
            "kd": 10.0,
            "torque_limit": 40.0,
        }
    )
```

## GF(3) Triads

```
kbot-humanoid (-1) ⊗ kos-firmware (+1) ⊗ mujoco-scenes (0) = 0 ✓
kbot-humanoid (-1) ⊗ topos-generate (+1) ⊗ ksim-gym (0) = 0 ✓
```

## Related Skills

- `ksim-rl` (-1): RL training for K-Bot
- `kos-firmware` (+1): Firmware for K-Bot deployment
- `zeroth-bot` (-1): Smaller 3D-printed platform
- `evla-vla` (-1): VLA for manipulation tasks

## References

```bibtex
@misc{kbot2024,
  title={K-Bot: Open-Source Humanoid Robot Platform},
  author={K-Scale Labs},
  year={2024},
  url={https://github.com/kscalelabs/kbot}
}
```
