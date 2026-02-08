---
name: gflownet
description: "Bengio's GFlowNets: Generative Flow Networks that sample proportionally to reward. Diversity over maximization for causal discovery and molecule design."
model: inherit
tools: read-only
---

# GFlowNet Skill

> *"Sample x with probability proportional to R(x), not just maximize R(x)."*
> — Yoshua Bengio

## Overview

**GFlowNets** (Generative Flow Networks) are a new paradigm:
- **RL**: Maximize expected reward → single optimal solution
- **MCMC**: Sample from distribution → slow mixing
- **GFlowNet**: Learn to sample P(x) ∝ R(x) → fast, diverse sampling

## Core Concept

```latex
GFlowNet Objective:

∀ terminal state x:  P_θ(x) = R(x) / Z

Where:
  P_θ(x) = probability of generating x via forward policy
  R(x) = unnormalized reward function
  Z = partition function (normalizing constant)

Key Insight: We DON'T need to know Z to train!
```

## Architecture

```
┌─────────────────────────────────────────────────────┐
│                    GFlowNet                         │
├─────────────────────────────────────────────────────┤
│  Initial State s₀                                   │
│        │                                            │
│        ▼                                            │
│  ┌─────────────┐                                    │
│  │ Forward     │  P_F(s' | s) = learned policy      │
│  │ Policy      │                                    │
│  └──────┬──────┘                                    │
│         │ sample action                             │
│         ▼                                            │
│  ┌─────────────┐                                    │
│  │ Transition  │  s → s'                            │
│  └──────┬──────┘                                    │
│         │                                            │
│         ▼                                            │
│  ┌─────────────┐                                    │
│  │ Terminal?   │───No──▶ continue                   │
│  └──────┬──────┘                                    │
│         │ Yes                                        │
│         ▼                                            │
│  ┌─────────────┐                                    │
│  │ R(x)        │  Eval