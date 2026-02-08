---
name: kbot-humanoid
description: K-Bot humanoid robot platform - hardware specs, MJCF models, and deployment configurations. The flagship K-Scale humanoid robot.
model: inherit
tools: read-only
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
<!-- kbot.mjcf excer