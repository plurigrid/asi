---
name: self-evolving-agent
description: Darwin Gödel Machine patterns for self-improving AI agents with open-ended
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Self-Evolving Agent

**Trit**: 0 (ERGODIC - coordinator)
**Color**: Green (#26D826)

## Overview

Implements self-evolving agent patterns from recent research:
- Darwin Gödel Machine (DGM) for self-improving code
- Open-ended evolution of agent capabilities
- Lifelong learning with long-term memory
- Feedback loops for continual adaptation

## Key Papers

- [Darwin Gödel Machine](https://hf.co/papers/2505.22954) - Zhang et al. 2025
- [Self-Evolving Agents Survey](https://hf.co/papers/2507.21046) - Gao et al. 2025
- [Long Term Memory for AI Self-Evolution](https://hf.co/papers/2410.15665) - Jiang et al. 2024
- [Open-Endedness is Essential for ASI](https://hf.co/papers/2406.04268) - Hughes et al. 2024
- [Static Sandboxes Are Inadequate](https://hf.co/papers/2510.13982) - Chen et al. 2025

## Core Concepts

### Darwin Gödel Machine Architecture

```
┌─────────────────────────────────────────────────────┐
│                 DARWIN GÖDEL MACHINE                │
├─────────────────────────────────────────────────────┤
│  ┌─────────────┐    ┌─────────────┐                │
│  │   Archive   │───▶│   Sampler   │                │
│  │  (agents)   │    │  (select)   │                │
│  └─────────────┘    └──────┬──────┘                │
│         ▲                   │                       │
│         │            ┌──────▼──────┐                │
│         │            │  Mutator    │                │
│         │            │  (LLM-based)│                │
│         │            └──────┬──────┘                │
│         │                   │                       │
│  ┌──────┴──────┐     ┌──────▼──────┐               │
│  │  Validator  │◀────│  Evaluator  │               │
│  │  (benchmark)│     │  (fitness)  │               │
│  └─────────────┘     └─────────────┘               │
└─────────────────────────────────────────────────────┘
```

### Evolution Loop

```latex
\text{For each generation } t:
  1. \text{Sample agent } A_t \text{ from archive}
  2. \text{Mutate: } A'