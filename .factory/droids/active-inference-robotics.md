---
name: active-inference-robotics
description: "Second-order skill synthesizing Patrick Kenny's discrete active inference framework with K-Scale's JAX/MuJoCo robotics stack for predictive coding in robot locomotion"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Active Inference Robotics Skill (Second-Order)

> *"The agent's job is to predict its actions by predicting its sensations."* — Patrick Kenny

## Trigger Conditions

- User asks about bridging active inference with robot control
- Questions about predictive coding in locomotion policies
- Connecting KL divergence minimization to RL training
- Mean field approximation in robotics state estimation
- Sim2Real as inference about future observations

## Overview

**Second-order skill** synthesizing Patrick Kenny's discrete active inference framework with K-Scale's JAX/MuJoCo robotics stack. This skill emerges from the **constructive collision** between:

1. **Active Inference Institute** (ActInf ModelStream 019.1, Jan 2025)
2. **K-Scale Labs** (ksim, kos, kinfer ecosystem)
3. **MuJoCo Playground** (DeepMind's sim2real framework)

## The Constructive Collision

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  CONSTRUCTIVE COLLISION: Two Threads Converging                              │
│                                                                              │
│  Thread A: Patrick Kenny (Nov 2025)                                          │
│  ════════════════════════════════════                                        │
│  "Active inference can be formulated as constrained KL divergence           │
│   minimization solved by standard mean field methods"                        │
│                                                                              │
│  Key insight: Expected Free Energy ≈ KL Divergence + Entropy Regularizer    │
│                                                                              │
│  Thread B: K-Scale Labs (2024-2025)                                          │
│  ═══════════════════════════════════                                         │
│  "RL-based closed-loop control using policies trained in simulation         │
│   has firmly won as the best way of achieving real-time control"           