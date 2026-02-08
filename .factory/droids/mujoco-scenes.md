---
name: mujoco-scenes
description: Package for creating different scenes in MuJoCo. Compose environments with objects, terrains, and obstacles for robot training.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# MuJoCo Scenes Skill

**Trit**: 0 (ERGODIC - coordination/infrastructure)
**Color**: #9FD875 (Soft Green)
**URI**: skill://mujoco-scenes#9FD875

## Overview

Package for composing MuJoCo scenes with objects, terrains, and obstacles. Enables diverse environment generation for robot training.

## Usage

```python
from mujoco_scenes import SceneBuilder, Terrain, Object

# Build a training scene
scene = SceneBuilder()

# Add terrain
scene.add_terrain(
    Terrain.FLAT,
    size=(10, 10),
    friction=1.0,
)

# Add obstacles
scene.add_object(
    Object.BOX,
    pos=(2, 0, 0.5),
    size=(0.5, 0.5, 0.5),
    color=(1, 0, 0, 1),
)

scene.add_object(
    Object.SPHERE,
    pos=(-1, 2, 0.3),
    radius=0.3,
    mass=0.5,
)

# Add terrain variations
scene.add_terrain(
    Terrain.STAIRS,
    pos=(5, 0, 0),
    step_height=0.15,
    step_count=5,
)

# Export to MJCF
mjcf = scene.to_mjcf()
```

## Terrain Types

```
┌─────────────────────────────────────────────────────────────┐
│                     TERRAIN TYPES                            │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  FLAT        ═══════════════════════════                    │
│                                                              │
│  STAIRS      ┌─┐                                            │
│            ┌─┘ └─┐                                          │
│          ┌─┘     └─┐                                        │
│                                                              │
│  RAMP        ╱╲                                             │
│             ╱  ╲                                            │
│                                                              │
│  ROUGH      ∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿                                │
│  (heightfield)                                               │
│                                                              │
│  GAPS       ═══   ═══   ═══   ═══               