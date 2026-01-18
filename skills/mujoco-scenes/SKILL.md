---
name: mujoco-scenes
description: Package for creating different scenes in MuJoCo. Compose environments with objects, terrains, and obstacles for robot training.
version: 1.0.0
category: robotics-simulation
author: K-Scale Labs
source: kscalelabs/mujoco-scenes
license: MIT
trit: 0
trit_label: ERGODIC
color: "#9FD875"
verified: false
featured: false
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
│  GAPS       ═══   ═══   ═══   ═══                           │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

## Domain Randomization

```python
from mujoco_scenes import DomainRandomizer

randomizer = DomainRandomizer(
    terrain_roughness=(0.0, 0.1),
    friction_range=(0.5, 1.5),
    object_position_noise=0.2,
    lighting_variation=True,
)

# Generate randomized scenes
for i in range(100):
    scene = randomizer.generate()
    scene.save(f"scene_{i}.mjcf")
```

## Integration with KSIM

```python
from ksim import RLTask
from mujoco_scenes import SceneBuilder

class WalkingWithObstacles(RLTask):
    def build_scene(self):
        scene = SceneBuilder()
        scene.add_terrain(Terrain.FLAT)
        scene.add_random_obstacles(count=10)
        return scene.to_mjcf()
```

## GF(3) Triads

This skill acts as the **ERGODIC (0)** coordinator:

```
ksim-rl (-1) ⊗ kos-firmware (+1) ⊗ mujoco-scenes (0) = 0 ✓
evla-vla (-1) ⊗ kos-firmware (+1) ⊗ mujoco-scenes (0) = 0 ✓
urdf2mjcf (-1) ⊗ kos-firmware (+1) ⊗ mujoco-scenes (0) = 0 ✓
kbot-humanoid (-1) ⊗ kos-firmware (+1) ⊗ mujoco-scenes (0) = 0 ✓
zeroth-bot (-1) ⊗ kos-firmware (+1) ⊗ mujoco-scenes (0) = 0 ✓
```

## Related Skills

- `ksim-rl` (-1): Uses scenes for training
- `kos-firmware` (+1): Robot firmware
- `urdf2mjcf` (-1): Model conversion
- `kbot-humanoid` (-1): K-Bot robot

## References

```bibtex
@misc{mujocoscenes2024,
  title={MuJoCo Scenes: Environment Composition for Robot Training},
  author={K-Scale Labs},
  year={2024},
  url={https://github.com/kscalelabs/mujoco-scenes}
}
```
