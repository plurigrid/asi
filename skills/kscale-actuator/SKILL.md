---
name: kscale-actuator
description: Rust library for controlling actuators (Robstride servo motors) on K-Scale robots. CAN bus communication, position/velocity/torque control.
version: 1.0.0
category: robotics-hardware
author: K-Scale Labs
source: kscalelabs/actuator
license: MIT
trit: -1
trit_label: MINUS
color: "#B9172E"
verified: false
featured: false
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
│  │                  robstride crate (Rust)                   │  │
│  │  ├── CAN bus communication                                │  │
│  │  ├── Motor protocol implementation                        │  │
│  │  └── Firmware interface                                   │  │
│  └──────────────────────────────────────────────────────────┘  │
│                            │                                    │
│                            ▼                                    │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                    Hardware                               │  │
│  │         Robstride Motors (CAN bus @ 1Mbps)               │  │
│  └──────────────────────────────────────────────────────────┘  │
└────────────────────────────────────────────────────────────────┘
```

## Rust API

```rust
use kscale_actuator::{ActuatorController, ActuatorConfig};

// Initialize controller
let config = ActuatorConfig {
    can_interface: "can0",
    motor_ids: vec![1, 2, 3, 4, 5, 6],
};

let mut controller = ActuatorController::new(config)?;

// Configure actuator
controller.configure(1, ActuatorParams {
    kp: 100.0,
    kd: 10.0,
    torque_limit: 40.0,
})?;

// Command position
controller.command_position(1, 0.5)?;  // radians

// Get state
let state = controller.get_state(1)?;
println!("Position: {}, Velocity: {}, Torque: {}", 
    state.position, state.velocity, state.torque);

// Low-level torque control
controller.command_torque(1, 5.0)?;  // Nm
```

## GF(3) Triads

```
kscale-actuator (-1) ⊗ kos-firmware (+1) ⊗ mujoco-scenes (0) = 0 ✓
```

## Related Skills

- `kos-firmware` (+1): Uses actuator crate via HAL
- `kbot-humanoid` (-1): K-Bot uses these actuators
- `robstride-driver` (-1): Low-level motor driver

## References

```bibtex
@misc{kscaleactuator2024,
  title={K-Scale Actuator Library},
  author={K-Scale Labs},
  year={2024},
  url={https://github.com/kscalelabs/actuator}
}
```


## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 6. Layering

**Concepts**: layered data, metadata, provenance, units

### GF(3) Balanced Triad

```
kscale-actuator (○) + SDF.Ch6 (+) + [balancer] (−) = 0
```

**Skill Trit**: 0 (ERGODIC - coordination)


### Connection Pattern

Layering adds metadata. This skill tracks provenance or annotations.
