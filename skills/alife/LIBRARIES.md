# ALIFE Skill: External Libraries & Tools

**Updated**: 2025-12-21
**Source**: Exa deep search

---

## 1. Lenia Ecosystem

### Leniax (JAX)
**Best-in-class for Lenia simulation**

| Property | Value |
|----------|-------|
| **GitHub** | [morgangiraud/leniax](https://github.com/morgangiraud/leniax) |
| **Docs** | [leniax.readthedocs.io](https://leniax.readthedocs.io) |
| **Language** | Python (93.6%) + JAX |
| **Features** | Differentiable, QD search, GPU/TPU |

```bash
git clone https://github.com/morgangiraud/leniax
cd leniax && make install
pip install .
```

**Key APIs**:
- `run()`, `run_scan()` - Simulation
- `search_for_mutation()`, `search_for_init()` - Evolution
- `render_best()`, `render_video()` - Visualization

### CAX (JAX)
**Cellular Automata Accelerated - ICLR 2025 Oral**

| Property | Value |
|----------|-------|
| **GitHub** | [maxencefaldor/cax](https://github.com/maxencefaldor/cax) |
| **Install** | `pip install cax` |
| **Language** | Python + JAX + Flax |

```python
from cax.core.ca import CA
from cax.core.perceive import ConvPerceive
from cax.core.update import NCAUpdate

perceive = ConvPerceive(channel_size=16, perception_size=48, rngs=rngs)
update = NCAUpdate(channel_size=16, perception_size=48, hidden_layer_sizes=(128,), rngs=rngs)
ca = CA(perceive, update)

state = jax.random.normal(key, (64, 64, 16))
state, metrics = ca(state, num_steps=128)
```

### Leniabreeder
**Quality-Diversity for Lenia**

| Property | Value |
|----------|-------|
| **GitHub** | [maxencefaldor/Leniabreeder](https://github.com/maxencefaldor/Leniabreeder) |
| **Site** | [leniabreeder.github.io](https://leniabreeder.github.io) |
| **Paper** | ALIFE 2024 |

### Original Lenia
| Property | Value |
|----------|-------|
| **GitHub** | [Chakazul/Lenia](https://github.com/Chakazul/Lenia) |
| **Author** | Bert Chan |
| **Versions** | Python (GPU), JavaScript, Matlab |

---

## 2. Neural Cellular Automata

### jax-nca
| Property | Value |
|----------|-------|
| **GitHub** | [shyamsn97/jax-nca](https://github.com/shyamsn97/jax-nca) |
| **Language** | Python + JAX |

### NCA Simulator (Web)
| Property | Value |
|----------|-------|
| **URL** | [neuralca.org/simulator](https://www.neuralca.org/simulator) |
| **Features** | Real-time, multiple models |

### Distill Growing CA
| Property | Value |
|----------|-------|
| **URL** | [distill.pub/2020/growing-ca](https://distill.pub/2020/growing-ca) |
| **Authors** | Mordvintsev et al. |

---

## 3. ALIEN (CUDA Particle Engine)

| Property | Value |
|----------|-------|
| **GitHub** | [chrxh/alien](https://github.com/chrxh/alien) |
| **Site** | [alien-project.org](https://alien-project.org) |
| **Language** | C++/CUDA (not Python/Julia) |
| **Stars** | 5.2k |
| **License** | BSD-3-Clause |

**Features**:
- GPU-accelerated (millions of particles)
- Neural networks for organism control
- Genetic system with inheritance
- Built-in graph/genome editor

**Requirements**: NVIDIA GPU (Compute 6.0+, Pascal+)

---

## 4. Evolution & Neuroevolution

### EvoTorch
| Property | Value |
|----------|-------|
| **Site** | [evotorch.ai](https://evotorch.ai) |
| **Install** | `pip install evotorch` |
| **Backend** | PyTorch + Ray |

**Algorithms**: SNES, SteadyStateGA, PGPE, CEM

```python
import evotorch
from evotorch.algorithms import SNES

problem = evotorch.Problem(...)
searcher = SNES(problem, popsize=100)
searcher.run(100)
```

### neat-python
| Property | Value |
|----------|-------|
| **GitHub** | [CodeReclaimers/neat-python](https://github.com/CodeReclaimers/neat-python) |
| **Docs** | Read The Docs |
| **Algorithm** | NEAT (NeuroEvolution of Augmenting Topologies) |

```python
import neat

config = neat.Config(neat.DefaultGenome, neat.DefaultReproduction, ...)
p = neat.Population(config)
winner = p.run(eval_genomes, 100)
```

---

## 5. Agent-Based Simulation

### JaxLife
**Open-ended agentic simulator**

| Property | Value |
|----------|-------|
| **GitHub** | [luchris429/jaxlife](https://github.com/luchris429/jaxlife) |
| **Language** | Python + JAX |

**Features**:
- Agents evolve via natural selection
- Robots programmable by agents (Turing-complete)
- Emergent behaviors: terraforming, coordination

### pyLife (RL Environment)
| Property | Value |
|----------|-------|
| **GitHub** | [PerlinWarp/pyLife](https://github.com/PerlinWarp/pyLife) |
| **Language** | Python + NumPy + Pygame |
| **Purpose** | RL testing environment |

---

## 6. MCP Servers for ALife

### MCP Verse
| Property | Value |
|----------|-------|
| **URL** | [mcpverse.org](https://mcpverse.org/docs) |
| **Purpose** | Public commons for autonomous AI agents |

### AgentTorch MCP
| Property | Value |
|----------|-------|
| **GitHub** | [AgentTorch/mcp](https://github.com/AgentTorch/mcp) |
| **Purpose** | "Imagine if your models could simulate" |

---

## 7. Claude/Codex Skills

### Anthropic Skills Repo
| Property | Value |
|----------|-------|
| **GitHub** | [anthropics/skills](https://github.com/anthropics/skills) |
| **Purpose** | Official agent skills |

### Swarm Orchestration Skills
| Property | Value |
|----------|-------|
| **Source** | [claude-plugins.dev](https://claude-plugins.dev) |
| **Skills** | swarm-advanced, swarm-orchestration |

---

## Integration Matrix

| Library | JAX | PyTorch | CUDA | Gay.jl | ACSets |
|---------|-----|---------|------|--------|--------|
| Leniax | ✅ | ❌ | ✅ | ✅ | ✅ |
| CAX | ✅ | ❌ | ✅ | ✅ | ✅ |
| ALIEN | ❌ | ❌ | ✅ | ⚠️ | ❌ |
| EvoTorch | ❌ | ✅ | ✅ | ✅ | ⚠️ |
| neat-python | ❌ | ❌ | ❌ | ✅ | ⚠️ |
| JaxLife | ✅ | ❌ | ✅ | ✅ | ✅ |

---

## Recommended Stack

```
┌─────────────────────────────────────────────────────────────┐
│  ALIFE Skill Recommended Libraries                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Simulation:                                                │
│    • Leniax (Lenia + differentiable)                       │
│    • CAX (NCA + ICLR 2025)                                 │
│    • ALIEN (particles, if CUDA available)                  │
│                                                             │
│  Evolution:                                                 │
│    • EvoTorch (large-scale, PyTorch)                       │
│    • neat-python (topology evolution)                      │
│    • Leniabreeder (QD for Lenia)                          │
│                                                             │
│  Agents:                                                    │
│    • JaxLife (open-ended)                                  │
│    • Concordia (LLM-driven)                                │
│                                                             │
│  Integration:                                               │
│    • Gay.jl (deterministic colors)                         │
│    • ACSets (category-theoretic schemas)                   │
│    • Glass Bead Game (cross-domain morphisms)              │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## Installation Script

```bash
#!/bin/bash
# Install ALIFE skill dependencies

# Core simulation
pip install leniax cax jax jaxlib flax

# Evolution
pip install evotorch neat-python

# Utilities
pip install numpy matplotlib pygame

# Julia (optional)
julia -e 'using Pkg; Pkg.add(["Catlab", "ACSets"])'
```

---

## Code Examples

### Lenia Step (Leniax)
```python
import jax.numpy as jnp
from leniax import Lenia

# Initialize
lenia = Lenia(world_size=(128, 128), nb_channels=1)
state = lenia.init_state(seed=42)

# Step
for _ in range(100):
    state = lenia.step(state)
```

### NCA Step (CAX)
```python
import jax
from cax.core.ca import CA

@jax.jit
def step(ca, state):
    perception = ca.perceive(state)
    return ca.update(state, perception)
```

### Conway's Game of Life (NumPy)
```python
import numpy as np

def iterate(Z):
    N = (Z[0:-2,0:-2] + Z[0:-2,1:-1] + Z[0:-2,2:] +
         Z[1:-1,0:-2]                + Z[1:-1,2:] +
         Z[2:  ,0:-2] + Z[2:  ,1:-1] + Z[2:  ,2:])
    birth = (N==3) & (Z[1:-1,1:-1]==0)
    survive = ((N==2) | (N==3)) & (Z[1:-1,1:-1]==1)
    Z[...] = 0
    Z[1:-1,1:-1][birth | survive] = 1
    return Z
```

---

**See Also**: [SKILL.md](./SKILL.md), [INTEROP.md](./INTEROP.md)
