---
name: forward-forward-learning
description: Hinton's Forward-Forward algorithm for local learning without backpropagation. Use for biologically plausible learning, on-chip training, memory-efficient networks, or parallel layer-wise training.
trit: 1
color: "#D82626"
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
        self.linear = nn.Linear(in_dim, out_dim)
        self.threshold = threshold
        self.optimizer = None  # Set per-layer optimizer
    
    def goodness(self, h):
        """Compute goodness: sum of squared activations."""
        return (h ** 2).sum(dim=-1)
    
    def forward(self, x, label=None):
        """Forward pass with optional label embedding."""
        if label is not None:
            # Embed label in first 10 dimensions (for MNIST)
            x = x.clone()
            x[:, :10] = 0
            x[:, label] = 1
        
        h = F.relu(self.linear(x))
        return h
    
    def train_step(self, x_pos, x_neg):
        """Local training step using FF algorithm."""
        h_pos = self.forward(x_pos)
        h_neg = self.forward(x_neg)
        
        g_pos = self.goodness(h_pos)
        g_neg = self.goodness(h_neg)
        
        # Loss: positive above threshold, negative below
        loss_pos = F.softplus(self.threshold - g_pos).mean()
        loss_neg = F.softplus(g_neg - self.threshold).mean()
        loss = loss_pos + loss_neg
        
        self.optimizer.zero_grad()
        loss.backward()
        self.optimizer.step()
        
        return loss.item(), h_pos.detach(), h_neg.detach()


class FFNetwork(nn.Module):
    """Full Forward-Forward network."""
    
    def __init__(self, dims, threshold=2.0, lr=0.03):
        super().__init__()
        self.layers = nn.ModuleList([
            FFLayer(dims[i], dims[i+1], threshold)
            for i in range(len(dims) - 1)
        ])
        
        # Per-layer optimizers
        for layer in self.layers:
            layer.optimizer = torch.optim.Adam(layer.parameters(), lr=lr)
    
    def train_epoch(self, dataloader, neg_generator):
        """Train all layers for one epoch."""
        total_loss = 0
        
        for x, y in dataloader:
            # Generate negative samples
            x_neg = neg_generator(x, y)
            
            # Embed labels
            x_pos = self.embed_label(x, y)
            x_neg = self.embed_label(x_neg, self.random_labels(y))
            
            # Train layer by layer
            h_pos, h_neg = x_pos, x_neg
            for layer in self.layers:
                loss, h_pos, h_neg = layer.train_step(h_pos, h_neg)
                total_loss += loss
        
        return total_loss
    
    def predict(self, x):
        """Predict by finding label with highest goodness."""
        best_label, best_goodness = None, -float('inf')
        
        for label in range(10):
            x_labeled = self.embed_label(x, label)
            h = x_labeled
            for layer in self.layers:
                h = layer(h)
            
            goodness = layer.goodness(h).mean()
            if goodness > best_goodness:
                best_label = label
                best_goodness = goodness
        
        return best_label


class SelfContrastiveFF(FFNetwork):
    """Self-Contrastive FF (Nature 2025)."""
    
    def __init__(self, dims, threshold=2.0):
        super().__init__(dims, threshold)
        
        # Learned negative generator
        self.neg_generator = nn.Sequential(
            nn.Linear(dims[0], dims[0]),
            nn.ReLU(),
            nn.Linear(dims[0], dims[0])
        )
    
    def generate_negatives(self, x_pos):
        """Generate negatives from positives."""
        # Method 1: Learned transformation
        x_neg = self.neg_generator(x_pos)
        
        # Method 2: Augmentation (simpler)
        # x_neg = x_pos + 0.1 * torch.randn_like(x_pos)
        
        return x_neg


class DistanceForwardLayer(FFLayer):
    """Distance-Forward layer (arXiv:2408.14925)."""
    
    def __init__(self, in_dim, out_dim, num_classes=10):
        super().__init__(in_dim, out_dim)
        self.class_centers = nn.Parameter(torch.randn(num_classes, out_dim))
    
    def distance_goodness(self, h, labels):
        """Goodness based on distance to class centers."""
        centers = self.class_centers[labels]
        return -((h - centers) ** 2).sum(dim=-1)  # Negative distance
    
    def train_step(self, x, labels):
        h = self.forward(x)
        goodness = self.distance_goodness(h, labels)
        loss = -goodness.mean()  # Minimize distance to correct center
        
        self.optimizer.zero_grad()
        loss.backward()
        self.optimizer.step()
        
        return loss.item(), h.detach()
```

### JAX Implementation (for Lenia/NCA integration)

```python
import jax
import jax.numpy as jnp
from flax import linen as nn

class FFLayerJAX(nn.Module):
    features: int
    threshold: float = 2.0
    
    @nn.compact
    def __call__(self, x):
        h = nn.Dense(self.features)(x)
        h = nn.relu(h)
        return h
    
    def goodness(self, h):
        return jnp.sum(h ** 2, axis=-1)


def ff_loss(params, model, x_pos, x_neg, threshold):
    """Forward-Forward loss in JAX."""
    h_pos = model.apply(params, x_pos)
    h_neg = model.apply(params, x_neg)
    
    g_pos = model.goodness(h_pos)
    g_neg = model.goodness(h_neg)
    
    loss_pos = jax.nn.softplus(threshold - g_pos).mean()
    loss_neg = jax.nn.softplus(g_neg - threshold).mean()
    
    return loss_pos + loss_neg


@jax.jit
def ff_train_step(params, opt_state, x_pos, x_neg, optimizer):
    loss, grads = jax.value_and_grad(ff_loss)(params, model, x_pos, x_neg, 2.0)
    updates, opt_state = optimizer.update(grads, opt_state)
    params = optax.apply_updates(params, updates)
    return params, opt_state, loss
```

## GF(3) Triads

This skill participates in balanced triads:

```
sheaf-cohomology (-1) ⊗ sheaf-laplacian-coordination (0) ⊗ forward-forward-learning (+1) = 0 ✓
proofgeneral-narya (-1) ⊗ unworld (0) ⊗ forward-forward-learning (+1) = 0 ✓
persistent-homology (-1) ⊗ open-games (0) ⊗ forward-forward-learning (+1) = 0 ✓
```

## Use Cases

### Memory-Efficient Training

```python
# No need to store activations for backward pass
model = FFNetwork([784, 500, 500, 10])
# Memory usage: O(layer_size) not O(depth * layer_size)
```

### Parallel Layer Training

```python
# Each layer can train independently
from concurrent.futures import ThreadPoolExecutor

def train_layer(layer, h_pos, h_neg):
    return layer.train_step(h_pos, h_neg)

with ThreadPoolExecutor() as executor:
    # All layers train in parallel
    futures = [executor.submit(train_layer, l, hp, hn) 
               for l, hp, hn in zip(layers, h_pos_list, h_neg_list)]
```

### On-Chip Learning

```python
# Suitable for neuromorphic hardware
# No weight transport problem (no backprop)
# Local synaptic updates only
```

### Integration with Neural CA

```python
# Forward-Forward for NCA rule learning
class FF_NCA(nn.Module):
    def __init__(self):
        self.perceive = FFLayer(48, 128)  # Sobel + identity
        self.update = FFLayer(128, 16)
    
    def step(self, grid):
        perception = self.perceive(grid)
        delta = self.update(perception)
        return grid + delta * self.stochastic_mask()
```

## Integration with Music-Topos

```clojure
;; In parallel_color_fork.clj
(defn ff-color-learning
  "Learn color preferences via Forward-Forward"
  [positive-colors negative-colors]
  (let [ff-layer (make-ff-layer 3 16)  ; RGB -> hidden
        goodness-pos (compute-goodness (forward ff-layer positive-colors))
        goodness-neg (compute-goodness (forward ff-layer negative-colors))]
    (local-update ff-layer goodness-pos goodness-neg)))
```

## Advantages Over Backpropagation

| Aspect | Backprop | Forward-Forward |
|--------|----------|-----------------|
| Memory | O(depth × width) | O(width) |
| Parallelism | Sequential layers | Parallel layers |
| Biological plausibility | Low | Higher |
| Weight transport | Required | Not needed |
| Gradient vanishing | Problem | Avoided |
| On-chip learning | Difficult | Natural |

## See Also

- `sheaf-laplacian-coordination` - Distributed coordination (complementary coordinator)
- `self-evolving-agent` - Continual adaptation (uses FF for local updates)
- `jaxlife-open-ended` - Open-ended evolution (FF for agent learning)
- `gay-mcp` - Deterministic colors for positive/negative sample generation

## References

```bibtex
@article{hinton2022forward,
  title={The Forward-Forward Algorithm: Some Preliminary Investigations},
  author={Hinton, Geoffrey E},
  journal={arXiv:2212.13345},
  year={2022}
}

@article{nature2025selfcontrastive,
  title={Self-Contrastive Forward-Forward Algorithm},
  journal={Nature Communications},
  year={2025}
}

@article{wu2024distance,
  title={Distance-Forward Learning},
  author={Wu, Yujie and others},
  journal={arXiv:2408.14925},
  year={2024}
}
```
