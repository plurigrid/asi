---
name: kscale
description: K-Scale Labs robotics skill collection - unified index for humanoid robot development, RL training, sim-to-real transfer, and deployment. Aggregates 9 specialized skills with GF(3) triadic organization.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# K-Scale Robotics Skill Collection

**Trit**: 0 (ERGODIC - coordination/infrastructure)
**Color**: #5B8DEE (Sky Blue)
**URI**: skill://kscale#5B8DEE

## Overview

This skill indexes the K-Scale Labs robotics ecosystem - a comprehensive open-source stack for building, training, and deploying humanoid robots. The collection follows GF(3) triadic organization with `kos-firmware` (+1) as the primary generator and `mujoco-scenes` (0) as the coordinator.

## Skill Inventory

```
┌────────────────────────────────────────────────────────────────────┐
│                    K-SCALE SKILL ECOSYSTEM                          │
├────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  PLUS (+1) - Generation/Construction                               │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │ kos-firmware        #79ED91  Robot firmware & gRPC services │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ERGODIC (0) - Coordination/Infrastructure                         │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │ mujoco-scenes       #9FD875  Scene composition for MuJoCo   │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  MINUS (-1) - Analysis/Verification                                 │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │ ksim-rl             #3A2F9E  RL training for locomotion     │   │
│  │ evla-vla            #DBA51D  Vision-language-action model   │   │
│  │ urdf2mjcf           #4615B7  URDF to MJCF conversion        │   │
│  │ kbot-humanoid       #5B45C2  K-Bot robot specifications     │   │
│  │ zeroth-bot          #8CC136  3D-printed humanoid platform   │   │
│  │ kscale-actuator     