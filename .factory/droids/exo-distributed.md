---
name: exo-distributed
description: Distributed LLM inference across Apple Silicon clusters with exo. Run models across Mac Studios via Thunderbolt RDMA, auto peer discovery, and MLX sharding. Use for multi-device inference, model parallelism, or building LLM clusters.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# exo-distributed Skill

> *"Run models across heterogeneous devices by forming GPU clusters with zero configuration."*

**Trit**: 0 (ERGODIC - coordination/orchestration)
**Color**: Neutral (60-180° hues)
**Source**: Random walk fusion over DuckLake interactions + DeepWiki exo-explore/exo

## Overview

[exo](https://github.com/exo-explore/exo) enables distributed LLM inference across multiple Apple Silicon devices:
- **Auto Peer Discovery**: Devices find each other automatically
- **RDMA over Thunderbolt 5**: Low-latency direct memory access
- **MLX Backend**: Native Apple Silicon acceleration via mlx.distributed
- **Pipeline + Tensor Parallelism**: Shard models across devices

## Quick Start

```bash
# Install exo
pip install exo-explore

# Start on first device (becomes master if elected)
exo

# Start on additional devices (auto-discovers peers)
exo

# Devices automatically form a cluster and expose OpenAI-compatible API
# Default: http://localhost:8080
```

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         EXO CLUSTER                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌────────────┐  Thunderbolt 5  ┌────────────┐                  │
│  │ Mac Studio │◄───── RDMA ────►│ Mac Studio │                  │
│  │   M4 Max   │                 │   M4 Max   │                  │
│  │ Layers 0-15│                 │Layers 16-31│                  │
│  └──────┬─────┘                 └──────┬─────┘                  │
│         │                              │                         │
│         └──────────────┬───────────────┘                         │
│                        │                                         │
│                   ┌────▼────┐                                    │
│                   │ Master  │                                    │
│                   │ (Elected)│            