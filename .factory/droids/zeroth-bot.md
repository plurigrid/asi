---
name: zeroth-bot
description: Zeroth Bot - 3D-printed open-source humanoid robot platform for sim-to-real and RL research. Affordable entry point for humanoid robotics.
model: inherit
tools: read-only
---

# Zeroth Bot Skill

**Trit**: -1 (MINUS - specification/verification)
**Color**: #8CC136 (Lime Green)
**URI**: skill://zeroth-bot#8CC136

## Overview

Zeroth Bot (Z-Bot) is a 3D-printed open-source humanoid robot platform designed for sim-to-real research and RL experimentation. An affordable entry point for humanoid robotics.

## Specifications

```
┌────────────────────────────────────────────────────────────────┐
│                      ZEROTH BOT (Z-BOT)                        │
├────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Height: ~40cm                                                 │
│  Weight: ~2kg                                                  │
│  DOF: 12 joints                                                │
│                                                                 │
│  Frame: 3D printed (PLA/PETG)                                  │
│  Actuators: Servo motors                                        │
│  Cost: ~$500 BOM                                               │
│                                                                 │
│  Ideal for:                                                     │
│  ├── Learning sim-to-real transfer                             │
│  ├── Testing RL policies at low cost                           │
│  ├── Educational robotics                                      │
│  └── Rapid prototyping                                         │
│                                                                 │
└────────────────────────────────────────────────────────────────┘
```

## Hardware BOM

| Component | Quantity | Notes |
|-----------|----------|-------|
| Servo motors | 12 | Standard hobby servos |
| 3D printed parts | Full set | STL files provided |
| MCU | 1 | ESP32 or Teensy |
| IMU | 1 | MPU6050 or similar |
| Power | 1 | 2S-3S LiPo |

## Training Pipeline

```python
from ksim.robots.zbot import ZBotConfig
from ksim import P