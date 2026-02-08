---
name: ksim-rl
description: RL training library for humanoid locomotion and manipulation built on MuJoCo and JAX. Provides PPO, AMP, and custom task abstractions for sim-to-real robotics policy training.
model: inherit
tools: read-only
---

# KSIM-RL Skill

**Trit**: -1 (MINUS - analysis/verification)
**Color**: #3A2F9E (Deep Purple)
**URI**: skill://ksim-rl#3A2F9E

## Overview

KSIM is K-Scale Labs' reinforcement learning library for humanoid robot locomotion and manipulation. Built on MuJoCo for physics simulation and JAX for hardware-accelerated training.

## Core Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                        KSIM ARCHITECTURE                        │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │
│  │  RLTask     │  │  PPOTask    │  │  AMPTask                │  │
│  │  (abstract) │──│  (PPO impl) │──│  (Adversarial Motion)   │  │
│  └─────────────┘  └─────────────┘  └─────────────────────────┘  │
│         │                                                        │
│         ▼                                                        │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │                    PhysicsEngine                             │ │
│  │  ┌───────────────┐  ┌───────────────────────────────┐       │ │
│  │  │ MujocoEngine  │  │ MjxEngine (JAX-accelerated)   │       │ │
│  │  └───────────────┘  └───────────────────────────────┘       │ │
│  └─────────────────────────────────────────────────────────────┘ │
│         │                                                        │
│         ▼                                                        │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │  Environment Components                                      │ │
│  │  • Actuators: Position, Velocity, Torque control            │ │
│  │  • Observations: Joint states, IMU, local view              │ │
│  │  • Rewards: Velocity tracking, gait, energy, stability      │ │
│  │  • Terminations: Fall detection, boundary violations        │ │
│  └─────────────────────────────────────────────────────────────┘ 