---
name: topomodelx-hodge
description: Hodge Laplacian neural networks for simplicial/cell/hypergraph complexes.
  PyTorch topological deep learning.
source: pyt-team/TopoModelX (tree-sitter extracted)
license: MIT
gf3_category: ZERO
---

# TopoModelX Hodge Laplacian Skill

> **Source**: [pyt-team/TopoModelX](https://github.com/pyt-team/TopoModelX) - tree-sitter extracted
> **Key directories**: `topomodelx/nn/simplicial/`, `topomodelx/nn/cell/`, `topomodelx/nn/hypergraph/`

## Architecture Overview

From tree-sitter analysis (120 Python files):

```
topomodelx/
├── nn/
│   ├── simplicial/     # 21 models (SAN, SCNN, SCN2, etc.)
│   ├── hypergraph/     # 22 models (AllSet, HMPNN, etc.)
│   ├── cell/           # 6 models (CAN, CCXN, etc.)
│   └── combinatorial/  # 2 models (CombinatorialNN)
├── base/               # Base layers (MessagePassing, etc.)
└── utils/              # Sparse tensor utilities
```

## Key Models (tree-sitter symbols)

### Simplicial Attention Network (SAN)

```python
# From topomodelx/nn/simplicial/san.py
class SAN:
    """Simplicial Attention Network.
    
    Methods (tree-sitter extracted):
    - __init__: Initialize layers
    - compute_projection_matrix: Build attention projections
    - forward: Message passing with Hodge Laplacian
    """
    
    def __init__(self, in_channels, hidden_channels, out_channels, n_layers=2):
        self.layers = nn.ModuleList([
            SANLayer(in_channels if i == 0 else hidden_channels, hidden_channels)
            for i in range(n_layers)
        ])
        self.out = nn.Linear(hidden_channels, out_channels)
    
    def forward(self, x_1, laplacian):
        """Forward pass on 1-simplices (edges).
        
        Parameters
        ----------
        x_1 : torch.Tensor, shape = (n_edges, in_channels)
            Input features on edges.
        laplacian : torch.Tensor, shape = (n_edges, n_edges)
            Hodge Laplacian of rank 1.
        """
        for layer in self.layers:
            x_1 = layer(x_1, laplacian)
        return self.out(x_1)
```

### Hodge Laplacian Construction

From tree-sitter search (`hodge_laplacian`):

```python
import toponetx as tnx
from topomodelx.utils.sparse import from_sparse

# Create simplicial complex
sc = tnx.SimplicialComplex([[0,1,2], [1,2,3], [2,3,4]])

# Get Hodge Laplacians for each rank
laplacian_0 = sc.hodge_laplacian_matrix(rank=0, weight=True)  # Graph Laplacian
laplacian_1 = sc.hodge_laplacian_matrix(rank=1, weight=True)  # Edge Laplacian
laplacian_2 = sc.hodge_laplacian_matrix(rank=2, weight=True)  # Triangle Laplacian

# Split into up/down components
laplacian_down_1 = sc.down_laplacian_matrix(rank=1)  # From triangles
laplacian_up_1 = sc.up_laplacian_matrix(rank=1)      # From vertices

# Convert to PyTorch sparse
L0 = from_sparse(laplacian_0)
L1_down = from_sparse(laplacian_down_1)
L1_up = from_sparse(laplacian_up_1)
L2 = from_sparse(laplacian_2)
```

## SCNN Layer (Simplicial Convolutional)

```python
# From topomodelx/nn/simplicial/scnn_layer.py

class SCNNLayer(nn.Module):
    """Simplicial Convolutional Neural Network layer.
    
    Performs convolution using Hodge Laplacian powers.
    """
    
    def __init__(self, in_channels, out_channels, conv_order=2):
        super().__init__()
        self.conv_order = conv_order
        self.weights = nn.ParameterList([
            nn.Parameter(torch.randn(in_channels, out_channels))
            for _ in range(conv_order + 1)
        ])
    
    def chebyshev_conv(self, conv_operator, x, conv_order):
        """Chebyshev polynomial convolution.
        
        Parameters
        ----------
        conv_operator : torch.sparse
            Hodge Laplacian or adjacency matrix.
        x : torch.Tensor
            Input features.
        conv_order : int
            Order of Chebyshev approximation.
        """
        # T_0(L) = I
        T_0 = x
        
        if conv_order == 0:
            return T_0 @ self.weights[0]
        
        # T_1(L) = L
        T_1 = torch.sparse.mm(conv_operator, x)
        out = T_0 @ self.weights[0] + T_1 @ self.weights[1]
        
        # T_k(L) = 2*L*T_{k-1} - T_{k-2}
        for k in range(2, conv_order + 1):
            T_2 = 2 * torch.sparse.mm(conv_operator, T_1) - T_0
            out = out + T_2 @ self.weights[k]
            T_0, T_1 = T_1, T_2
        
        return out
    
    def forward(self, x, laplacian):
        return self.chebyshev_conv(laplacian, x, self.conv_order)
```

## Multi-Rank Message Passing (SCCNN)

```python
# From topomodelx/nn/simplicial/sccnn_layer.py

class SCCNNLayer(nn.Module):
    """Simplicial Complex Convolutional Neural Network.
    
    Message passing across multiple ranks (0, 1, 2 simplices).
    """
    
    def forward(self, x_0, x_1, x_2, laplacian_all, incidence_all):
        """
        Parameters (from tree-sitter docstring):
        - laplacian_0: torch.sparse, graph Laplacian
        - laplacian_down_1: torch.sparse, 1-Hodge laplacian (lower part)
        - laplacian_up_1: torch.sparse, 1-Hodge laplacian (upper part)
        - laplacian_2: torch.sparse, 2-Hodge laplacian
        """
        L0, L1_down, L1_up, L2 = laplacian_all
        B1, B2 = incidence_all
        
        # Intra-rank convolution
        x_0_out = self.conv_0(L0, x_0)
        x_1_out = self.conv_1_down(L1_down, x_1) + self.conv_1_up(L1_up, x_1)
        x_2_out = self.conv_2(L2, x_2)
        
        # Inter-rank message passing via incidence
        x_0_out += B1.T @ x_1  # Edges → Vertices
        x_1_out += B1 @ x_0 + B2.T @ x_2  # Vertices/Triangles → Edges
        x_2_out += B2 @ x_1  # Edges → Triangles
        
        return x_0_out, x_1_out, x_2_out
```

## GF(3) Integration

```python
def hodge_rank_to_trit(rank: int, total_ranks: int) -> int:
    """Map Hodge rank to GF(3) trit."""
    if total_ranks <= 1:
        return 0
    
    # Balanced assignment across ranks
    position = rank / (total_ranks - 1)  # [0, 1]
    
    if position < 0.33:
        return -1  # MINUS: lower ranks (verification)
    elif position > 0.66:
        return 1   # PLUS: higher ranks (generation)
    else:
        return 0   # ZERO: middle ranks (coordination)


def verify_laplacian_gf3_flow(laplacians: list, features: list) -> bool:
    """Verify GF(3) conservation across Laplacian message passing."""
    trits = [hodge_rank_to_trit(i, len(laplacians)) for i in range(len(laplacians))]
    
    # Check: information flow balanced
    total_trit = sum(trits)
    return total_trit % 3 == 0


# Example with 3 ranks (0, 1, 2)
laplacians = [L0, L1, L2]
trits = [-1, 0, 1]  # MINUS, ZERO, PLUS
assert sum(trits) % 3 == 0  # Conservation holds
```

## Complete Training Example

```python
import torch
import toponetx as tnx
from topomodelx.nn.simplicial.san import SAN
from topomodelx.utils.sparse import from_sparse

# Create dataset
sc = tnx.SimplicialComplex([[0,1,2], [1,2,3], [2,3,4], [3,4,5]])
x_1 = torch.randn(sc.number_of_cells(1), 16)  # Edge features
y = torch.randint(0, 2, (sc.number_of_cells(1),))  # Edge labels
laplacian = from_sparse(sc.hodge_laplacian_matrix(rank=1))

# Model
model = SAN(in_channels=16, hidden_channels=32, out_channels=2)
optimizer = torch.optim.Adam(model.parameters(), lr=0.01)
criterion = torch.nn.CrossEntropyLoss()

# Training loop
for epoch in range(100):
    optimizer.zero_grad()
    out = model(x_1, laplacian)
    loss = criterion(out, y)
    loss.backward()
    optimizer.step()
    
    if epoch % 10 == 0:
        print(f"Epoch {epoch}, Loss: {loss.item():.4f}")
```

## Links

- [TopoModelX](https://github.com/pyt-team/TopoModelX)
- [TopoNetX (TopologyX)](https://github.com/pyt-team/toponetx)
- [TopoBenchmarkX](https://github.com/pyt-team/TopoBenchmarkX)
- [Hodge Laplacians on Graphs](https://arxiv.org/abs/1802.04314)

## Commands

```bash
just topomodelx-san-train     # Train SAN model
just topomodelx-scnn-demo     # SCNN convolution demo
just topomodelx-hodge-viz     # Visualize Hodge decomposition
just topomodelx-gf3-verify    # GF(3) flow verification
```

---

*GF(3) Category: ZERO (Coordination) | Hodge Laplacian neural networks*