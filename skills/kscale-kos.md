# K-Scale KOS Skill

> *"A general-purpose, configurable framework for robot firmware"*

## Trigger Conditions

- User asks about robot operating systems, firmware, or low-level control
- Questions about actuator control, IMU integration, motor drivers
- gRPC service interfaces for robot hardware
- Real-time control loops, servo calibration

## Overview

**KOS** (K-Scale Operating System) is a Rust-based robot firmware framework providing:

1. **Hardware Abstraction**: Unified interface for actuators, sensors, IMUs
2. **gRPC Services**: Remote procedure calls for robot control
3. **Real-time Control**: Low-latency servo loops
4. **Calibration Tools**: Servo tuning and parameter management

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│  KOS Architecture                                                        │
│                                                                          │
│  ┌──────────────┐      gRPC      ┌──────────────┐                       │
│  │   Client     │◀──────────────▶│  KOS Server  │                       │
│  │  (Python)    │                │   (Rust)     │                       │
│  └──────────────┘                └──────┬───────┘                       │
│                                         │                                │
│                    ┌────────────────────┼────────────────────┐          │
│                    ▼                    ▼                    ▼          │
│             ┌──────────┐        ┌──────────┐        ┌──────────┐       │
│             │ Actuator │        │   IMU    │        │  Policy  │       │
│             │ Service  │        │ Service  │        │ Service  │       │
│             └────┬─────┘        └────┬─────┘        └────┬─────┘       │
│                  │                   │                   │              │
│                  ▼                   ▼                   ▼              │
│             ┌──────────────────────────────────────────────┐           │
│             │              Hardware Layer                   │           │
│             │  (CAN bus, SPI, I2C, UART)                   │           │
│             └──────────────────────────────────────────────┘           │
└─────────────────────────────────────────────────────────────────────────┘
```

## Key Services

| Service | Purpose | Methods |
|---------|---------|---------|
| `ActuatorService` | Motor control | `GetState`, `SetPosition`, `Calibrate` |
| `IMUService` | Orientation sensing | `GetQuaternion`, `GetAngularVelocity` |
| `PolicyService` | RL policy execution | `LoadModel`, `Step`, `GetAction` |
| `CalibrationService` | Servo tuning | `GetCalibrationState`, `SetParameters` |

## Language & Stack

- **Primary**: Rust (safe, fast, real-time capable)
- **Protocol**: gRPC/protobuf for client communication
- **Bindings**: Python SDK via `kos-python`

## Release History

| Version | Date | Highlights |
|---------|------|------------|
| 0.7.10 | 2025-05-26 | Extended Actuator State Response |
| 0.7.9 | 2025-05-14 | New PolicyService |
| 0.7.8 | 2025-05-06 | GetCalibrationState |
| 0.7.7 | 2025-05-04 | Parameter Dump API |

## GF(3) Trit Assignment

```
Trit: -1 (MINUS)
Role: Verification/Validation (firmware = critical path)
Color: #7758D6
URI: skill://kscale-kos#7758D6
```

### Balanced Triads

```
kscale-kos (-1) ⊗ kscale-ksim (0) ⊗ gym (+1) = 0 ✓
kscale-kos (-1) ⊗ embedded-rust (0) ⊗ robotics-gen (+1) = 0 ✓
```

## Related Skills

- `kscale-ksim`: Simulation training (policies deploy to KOS)
- `kscale-kinfer`: Model inference (runs on KOS)
- `rust`: Systems programming language
- `grpc`: Remote procedure calls

## Example Usage

```python
import kos

# Connect to robot
client = kos.Client("192.168.1.100:50051")

# Get actuator state
state = client.actuator.get_state(joint_ids=[1, 2, 3])
print(f"Positions: {state.positions}")

# Set position command
client.actuator.set_position(
    joint_id=1,
    position=1.57,  # radians
    velocity=0.5    # rad/s limit
)

# Load and run policy
client.policy.load_model("walking_v2.onnx")
while True:
    obs = client.get_observation()
    action = client.policy.step(obs)
    client.actuator.set_positions(action)
```

## References

- [kscalelabs/kos](https://github.com/kscalelabs/kos) - Main repository (76 stars)
- [kscalelabs/kos-sim](https://github.com/kscalelabs/kos-sim) - Simulation backend
- [kscalelabs/kos-kbot](https://github.com/kscalelabs/kos-kbot) - K-Bot implementation
