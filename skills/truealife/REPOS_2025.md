# TrueALife: 2025 Repository Deep Dive

## ASAL - Automating the Search for Artificial Life

**Repository**: https://github.com/SakanaAI/asal
**Paper**: arXiv:2412.17799 (Dec 2024)
**Demo**: https://asal.sakana.ai/

### Key Innovation

Uses vision-language foundation models (GPT-4V, Claude) to automatically discover interesting ALife simulations:

1. **Supervised Target Search**: Find simulations matching text prompts
2. **Open-Ended Exploration**: Discover temporally novel dynamics
3. **Diversity Illumination**: Map entire space of interesting simulations

### Supported Substrates

| Substrate | Discovery Type |
|-----------|----------------|
| Lenia | Self-organizing cell-like patterns |
| Boids | Exotic flocking behaviors |
| Particle Life | Dynamic ecosystems |
| Particle Life++ | Agentic pattern emergence |
| Game of Life | Novel CA rules (more expressive than Conway) |
| Neural CA | Learned self-organization |

### Installation

```bash
git clone https://github.com/SakanaAI/asal
cd asal
pip install -e .

# Run discovery
python -m asal.discover --substrate lenia --objective "cells dividing"
```

---

## CAX - Cellular Automata Accelerated

**Repository**: https://github.com/maxencefaldor/cax
**Status**: ICLR 2025 Oral
**Framework**: JAX

### Features

- 100x+ speedup over NumPy implementations
- Differentiable CA for gradient-based learning
- Supports Elementary CA, Lenia, NCA, custom rules
- TPU/GPU automatic parallelization

### Code Example

```python
import jax
import jax.numpy as jnp
from cax import CA, NCA, Lenia

# Elementary CA Rule 110
ca = CA.from_rule(110)
key = jax.random.PRNGKey(0)
state = ca.init(key, shape=(100,))

# Run 1000 steps
def scan_fn(state, _):
    return ca.step(state), state
final, trajectory = jax.lax.scan(scan_fn, state, None, 1000)

# Neural CA
nca = NCA(hidden_channels=16, fire_rate=0.5)
params = nca.init(key, jnp.zeros((64, 64, 16)))

# Lenia
lenia = Lenia.from_params(R=13, T=10, mu=0.15, sigma=0.017)
```

---

## Flow-Lenia

**Paper**: arXiv:2506.08569 (June 2025)
**Key**: Mass-conserving Lenia with velocity fields

### Equations

```latex
% Velocity field from kernel convolution
\vec{v}(x) = \nabla G(K * A^t)

% Mass-conserving update (continuity equation)
A^{t+1} = A^t - \nabla \cdot (A^t \cdot \vec{v})

% Multispecies extension
A_i^{t+1} = A_i^t - \nabla \cdot \left(A_i^t \cdot \sum_j w_{ij} \vec{v}_j\right)
```

### AI Scientist Method

Uses Intrinsically Motivated Goal Exploration Processes (IMGEPs) to:
- Systematically discover novel dynamics
- Navigate large-scale parameter spaces
- Identify phase transitions and emergent behaviors

---

## ARC-NCA / EngramNCA

**Paper**: arXiv:2505.08778 (May 2025)
**Benchmark**: ARC (Abstraction and Reasoning Corpus)

### Performance

| System | ARC Public | Compute |
|--------|-----------|---------|
| GPT-4.5 | ~17% | 1000x |
| EngramNCA v3 | 27% | 1x |

### Architecture

```python
class EngramNCA:
    """NCA with hidden memory for ARC tasks."""

    def __init__(self, hidden_dim=64):
        self.hidden = None  # Persistent engram

    def step(self, visible, task_encoding):
        # Hidden state carries memory across steps
        h_new = self.update_hidden(visible, self.hidden, task_encoding)
        v_new = self.update_visible(visible, h_new)
        self.hidden = h_new
        return v_new
```

---

## JaxLife

**Repository**: https://github.com/luchris429/JaxLife
**Focus**: Open-ended agentic evolution

### Components

1. **Agents**: RNN-parameterized, natural selection
2. **Robots**: Turing-complete programmable machines
3. **Terrain**: Dynamic climate/weather system

### Architecture

- Separate encoders for entity types
- Self-attention for nearby entities
- Cross-attention with agent embedding
- Terrain processed by dedicated encoder

---

## Tölvera

**Repository**: https://github.com/afhverjuekki/tolvera
**Focus**: Live-coding ALife for music/art

### Features

- Real-time OSC integration
- Interactive machine learning
- Algorave-ready
- Self-organizing systems for audiovisual performance

---

## ALIEN (Updated 2025)

**Repository**: https://github.com/chrxh/alien
**Stars**: 5.3k (highest in category)
**Winner**: ALIFE 2024 Virtual Creatures Competition

### 2025 Updates

- Improved particle physics
- Neural evolution enhancements
- Better GPU memory management
- New creature templates

---

## Concordia (DeepMind)

**Repository**: https://github.com/google-deepmind/concordia
**Focus**: Generative agent-based models with LLMs

### Use Cases

- Multi-agent social simulation
- Emergent behavior from LLM interactions
- Narrative-driven world modeling

---

## Coming in 2025-2026

### Announced/Expected

| Project | Expected | Focus |
|---------|----------|-------|
| Lenia 3.0 | 2025 | 3D continuous CA |
| ASAL-Pro | 2025 | Multi-modal FM integration |
| OpenEnded-Evolution | 2026 | Benchmark suite |
| ALife-Bench | 2025 | Standardized evaluation |

### Research Directions

1. **FM + ALife**: Foundation models guiding/evaluating ALife
2. **Differentiable Everything**: Gradient-based CA/agent optimization
3. **Open-Endedness Metrics**: Quantifying novelty generation
4. **Hybrid Bioengineering**: Wetware + software integration
5. **Distributed ALife**: Large-scale multi-node simulations
