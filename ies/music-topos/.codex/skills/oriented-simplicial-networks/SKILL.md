# Oriented Simplicial Networks

**Category:** Phase 3 Core - Geometric Deep Learning
**Status:** Skeleton Implementation
**Dependencies:** `categorical-composition`, `persistent-homology`

## Overview

Implements directional simplicial neural networks (Dir-SNNs) with asymmetric message passing operators, E(n)-equivariance constraints, and persistent homology tracking for topological feature learning.

## Capabilities

- **Directional Message Passing**: Asymmetric operators respecting simplex orientation
- **E(n)-Equivariance**: Rotation/translation invariant representations
- **Persistent Homology**: Track topological features during training
- **Simplicial Attention**: Higher-order attention mechanisms on simplicial complexes

## Core Components

1. **Simplicial Complex Builder** (`simplicial_complex.jl`)
   - Construct oriented simplicial complexes from data
   - Boundary operator computation
   - Coboundary and Laplacian matrices

2. **Dir-SNN Layers** (`dirsnn_layers.jl`)
   - Asymmetric message passing on simplices
   - E(n)-equivariant convolutions
   - Higher-order pooling operators

3. **Persistent Homology Tracker** (`persistent_homology.jl`)
   - Compute persistence diagrams during forward pass
   - Track birth/death of topological features
   - Bottleneck/Wasserstein distance metrics

4. **Training Loop** (`train_dirsnn.jl`)
   - Integration with Flux.jl
   - Topologically-aware loss functions
   - Gradient flow on simplicial manifolds

## Integration Points

- **Input from**: `sheaf-theoretic-coordination` (sheaf structures on simplicial complexes)
- **Output to**: `categorical-composition` (functorial network composition)
- **Coordinates with**: `formal-verification-ai` (verify topological invariants)

## Usage

```julia
using OrientedSimplicialNetworks

# Build simplicial complex from point cloud
complex = SimplicialComplex(points, max_dimension=2)

# Create Dir-SNN model
model = DirSNN([
    SimplicialConv(in_features=3, out_features=16, dimension=0),
    SimplicialConv(in_features=16, out_features=32, dimension=1),
    SimplicialPooling(dimension=1)
])

# Train with persistent homology tracking
train!(model, complex, labels; track_topology=true)
```

## References

- Bodnar et al. "Weisfeiler and Lehman Go Cellular" (NeurIPS 2021)
- Hajij et al. "Topological Deep Learning" (Nature 2023)
- Carlsson "Topology and Data" (AMS 2009)

## Implementation Status

- [x] Core data structures
- [x] Basic message passing
- [ ] Full E(n)-equivariance
- [ ] Persistent homology integration
- [ ] Benchmark suite
