---
name: urdf2mjcf
description: Convert URDF robot descriptions to MJCF format for MuJoCo simulation. Handles meshes, joints, actuators, and collision geometries.
model: inherit
tools: read-only
---

# URDF2MJCF Skill

**Trit**: -1 (MINUS - analysis/transformation)
**Color**: #4615B7 (Deep Violet)
**URI**: skill://urdf2mjcf#4615B7

## Overview

Convert URDF (Unified Robot Description Format) files to MJCF (MuJoCo XML Format) for simulation in MuJoCo and MJX. Handles meshes, joints, actuators, and collision geometries.

## Usage

```bash
# CLI conversion
urdf2mjcf robot.urdf --output robot.mjcf

# With options
urdf2mjcf robot.urdf \
    --output robot.mjcf \
    --mesh-dir ./meshes \
    --add-actuators \
    --collision-margin 0.001
```

```python
from urdf2mjcf import convert

# Programmatic conversion
mjcf_xml = convert(
    urdf_path="robot.urdf",
    mesh_dir="./meshes",
    add_actuators=True,
    collision_margin=0.001,
)

# Save to file
with open("robot.mjcf", "w") as f:
    f.write(mjcf_xml)
```

## Features

- **Mesh Handling**: Converts STL/OBJ meshes, scales appropriately
- **Joint Mapping**: URDF revolute/prismatic → MJCF hinge/slide
- **Actuator Generation**: Auto-generates position/velocity actuators
- **Collision Geometry**: Convex decomposition, margin adjustment
- **Inertia Cleanup**: Fixes common URDF inertia issues

## Pipeline

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│  URDF File  │───▶│  urdf2mjcf  │───▶│  MJCF File  │
│  (ROS/SDF)  │    │  Converter  │    │  (MuJoCo)   │
└─────────────┘    └─────────────┘    └─────────────┘
       │                  │                  │
       ▼                  ▼                  ▼
   Meshes STL        Link transforms     Physics props
   Joint limits      Mass/inertia        Actuator defs
   Visual geom       Collision geom      Sensor defs
```

## GF(3) Triads

```
urdf2mjcf (-1) ⊗ kos-firmware (+1) ⊗ mujoco-scenes (0) = 0 ✓
```

## Related Skills

- `ksim-rl` (-1): Uses converted MJCF for training
- `kos-firmware` (+1): Robot firmware
- `mujoco-scenes` (0): Scene composition
- `kbot-humanoid` (-1): K-Bot robot model

## References

```bibtex
@misc{urdf2mjcf2024,
  title={URDF to MJCF C