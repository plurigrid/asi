---
name: kscale-actuator
description: Rust library for controlling actuators (Robstride servo motors) on K-Scale robots. CAN bus communication, position/velocity/torque control.
model: inherit
tools: read-only
---

# K-Scale Actuator Skill

**Trit**: -1 (MINUS - hardware interface/verification)
**Color**: #B9172E (Deep Red)
**URI**: skill://kscale-actuator#B9172E

## Overview

Rust library for controlling actuators on K-Scale robots. Supports Robstride servo motors with CAN bus communication. Provides position, velocity, and torque control modes.

## Architecture

```
┌────────────────────────────────────────────────────────────────┐
│                    ACTUATOR CONTROL STACK                       │
├────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                    KOS Firmware                           │  │
│  │                 ActuatorService (gRPC)                    │  │
│  └──────────────────────────────────────────────────────────┘  │
│                            │                                    │
│                            ▼                                    │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                  actuator crate (Rust)                    │  │
│  │  ┌─────────────────────────────────────────────────────┐ │  │
│  │  │  ActuatorController                                 │ │  │
│  │  │  ├── configure(kp, kd, torque_limit)               │ │  │
│  │  │  ├── command_position(joint_id, position)          │ │  │
│  │  │  ├── command_velocity(joint_id, velocity)          │ │  │
│  │  │  ├── command_torque(joint_id, torque)              │ │  │
│  │  │  └── get_state() -> ActuatorState                  │ │  │
│  │  └─────────────────────────────────────────────────────┘ │  │
│  └──────────────────────────────────────────────────────────┘  │
│                            │                                    │
│                            ▼                                    │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                  robstr