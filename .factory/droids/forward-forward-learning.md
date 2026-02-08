---
name: forward-forward-learning
description: Hinton's Forward-Forward algorithm for local learning without backpropagation.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Forward-Forward Learning

**Trit**: +1 (PLUS - generator)
**Color**: Red (#D82626)

## Overview

Implements Geoffrey Hinton's Forward-Forward (FF) algorithm (2022) and extensions:
- Local layer-wise learning without backpropagation
- Contrastive positive/negative data passes
- Goodness functions for layer-wise objectives
- Memory-efficient and parallelizable training

## Key Papers

- [The Forward-Forward Algorithm](https://arxiv.org/abs/2212.13345) - Hinton 2022
- [Self-Contrastive Forward-Forward](https://nature.com/articles/s41467-025-61037-0) - Nature 2025
- [Distance-Forward Learning](https://arxiv.org/abs/2408.14925) - Wu et al. 2024
- [Forward Learning of GNNs](https://proceedings.iclr.cc/paper_files/paper/2024/file/63f6b8c3b9247111b4f468d26782902e-Paper-Conference.pdf) - ICLR 2024
- [VFF-Net](https://www.sciencedirect.com/science/article/abs/pii/S0893608025005775) - 2025

## Core Concepts

### Forward-Forward Algorithm

Replace backprop with two forward passes:

```latex
\text{Positive pass}: x^+ \text{ (real data)} \rightarrow \text{high goodness}
\text{Negative pass}: x^- \text{ (generated/corrupted)} \rightarrow \text{low goodness}

\text{Goodness function}: G(h) = \sum_i h_i^2  \text{ (sum of squared activations)}

\text{Layer objective}: \max G(h^+) - G(h^-)  \text{ subject to threshold } \theta
```

### Layer-wise Training

Each layer trains independently:

```
Layer L objective:
  P(positive | h_L) = σ(G(h_L) - θ)
  
Loss: -log P(positive | h_L^+) - log(1 - P(positive | h_L^-))
```

### Self-Contrastive Extension (Nature 2025)

Generate negative samples from the network itself:

```latex
x^- = \text{augment}(x^+) \text{ or } x^- = G_\phi(z) \text{ (learned generator)}
```

## API

### Python Implementation

```python
import torch
import torch.nn as nn
import torch.nn.functional as F

class FFLayer(nn.Module):
    """Forward-Forward layer with local learning."""
    
    def __init__(self, in_dim, out_dim, threshold=2.0):
        super().__init__()
 