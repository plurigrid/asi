# Feedforward Learning Local

**Category:** Phase 3 Core - Alternative Learning Paradigms
**Status:** Skeleton Implementation
**Dependencies:** None (standalone learning framework)

## Overview

Implements forward-forward (FF) learning algorithm and variants that eliminate backpropagation through local, layer-wise contrastive objectives. Each layer learns to distinguish positive from negative data independently.

## Capabilities

- **Forward-Forward Algorithm**: Hinton's layer-local learning
- **Contrastive Objectives**: Positive/negative data discrimination
- **No Backprop**: Purely feedforward gradient computation
- **Statistical Communication**: Inter-layer coordination via activity statistics

## Core Components

1. **FF Layer** (`ff_layer.jl`)
   - Local goodness function per layer
   - Positive/negative data generation
   - Layer-wise gradient updates

2. **Contrastive Learning** (`contrastive_learning.jl`)
   - Contrastive divergence variants
   - Energy-based formulations
   - Hybrid supervised/unsupervised objectives

3. **Statistical Coordination** (`statistical_coordination.jl`)
   - Activity normalization between layers
   - Whitening and decorrelation
   - Predictive coding integration

4. **FF Network** (`ff_network.jl`)
   - Multi-layer FF architecture
   - Inference and training loops
   - Comparison with backprop baselines

## Integration Points

- **Input from**: Raw data (no dependencies on other skills)
- **Output to**: `emergent-role-assignment` (decentralized learning signals)
- **Coordinates with**: `categorical-composition` (compositional learning)

## Usage

```julia
using FeedforwardLearningLocal

# Create FF network
network = FFNetwork([
    FFLayer(input_dim=784, hidden_dim=500, threshold=2.0),
    FFLayer(input_dim=500, hidden_dim=500, threshold=2.0),
    FFLayer(input_dim=500, hidden_dim=10, threshold=1.0)
])

# Train on MNIST
for (x_pos, y) in train_data
    # Generate negative data by corrupting label
    x_neg = overlay_wrong_label(x_pos, y)

    # Local learning at each layer
    train_step!(network, x_pos, x_neg)
end

# Inference
predictions = predict(network, test_data)
```

## References

- Hinton "The Forward-Forward Algorithm" (2022)
- LeCun et al. "A Tutorial on Energy-Based Learning" (2006)
- Nokland & Eidnes "Training Neural Networks with Local Error Signals" (ICML 2019)

## Implementation Status

- [x] Basic FF layer implementation
- [x] Positive/negative data generation
- [ ] Multiple variants (supervised, unsupervised)
- [ ] Benchmark against backprop
- [ ] Integration with predictive coding
