---
name: jaxlife-open-ended
description: JaxLife open-ended agentic simulator for emergent behavior, tool use,
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# JaxLife Open-Ended

**Trit**: +1 (PLUS - generator)
**Color**: Red (#D82626)

## Overview

Implements patterns from JaxLife and related open-ended ALife simulators:
- Embodied agents with neural network controllers
- Turing-complete programmable environments
- Emergent communication, agriculture, and tool use
- Open-ended cultural and technological accumulation

## Key Papers

- [JaxLife: An Open-Ended Agentic Simulator](https://hf.co/papers/2409.00853) - Lu et al. 2024
- [Biomaker CA](https://hf.co/papers/2307.09320) - Randazzo & Mordvintsev 2023
- [LifeGPT](https://hf.co/papers/2409.12182) - Berkovich & Buehler 2024
- [The Station](https://hf.co/papers/2511.06309) - Chung & Du 2025
- [Static Sandboxes Are Inadequate](https://hf.co/papers/2510.13982) - Chen et al. 2025

## Core Concepts

### JaxLife Environment

```
┌─────────────────────────────────────────────────────┐
│                   JAXLIFE WORLD                     │
├─────────────────────────────────────────────────────┤
│  ┌─────────┐  ┌─────────┐  ┌─────────┐             │
│  │ Agent 1 │  │ Agent 2 │  │ Agent N │  ...        │
│  │  (NN)   │  │  (NN)   │  │  (NN)   │             │
│  └────┬────┘  └────┬────┘  └────┬────┘             │
│       │            │            │                   │
│       ▼            ▼            ▼                   │
│  ┌─────────────────────────────────────────────┐   │
│  │              PROGRAMMABLE GRID               │   │
│  │   (Turing-complete, supports computation)    │   │
│  └─────────────────────────────────────────────┘   │
│       │                                             │
│       ▼                                             │
│  ┌─────────────────────────────────────────────┐   │
│  │         EMERGENT BEHAVIORS                   │   │
│  │  • Communication protocols                   │   │
│  │  • Agriculture / resource management         │   │
│  │  • Tool use and construction                 │   │
│  │  • Cultural inheritance                      │   │
