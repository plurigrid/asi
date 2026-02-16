---
name: topological-dataloader
description: 'Batched heterogeneous topological complex dataloaders for TopoModelX.
  Addresses pyt-team/TopoModelX#325 and #243.'
source: pyt-team/TopoModelX + GitHub issues research
license: MIT
gf3_category: MINUS
---

# Topological Dataloader Skill

> **Addresses**: [TopoModelX #325](https://github.com/pyt-team/TopoModelX/issues/325) (batch heterogeneous complexes) and [#243](https://github.com/pyt-team/TopoModelX/issues/243) (dataloader blocking production)

## Problem Statement

TopoModelX currently lacks efficient dataloaders for:
1. **Heterogeneous complexes** - varying sizes within batches
2. **Mixed topologies** - simplicial + cell + hypergraph in same dataset
3. **Streaming large datasets** - memory-efficient loading

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                 TopologicalDataLoader                        │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐          │
│  │ Simplicial  │  │    Cell     │  │ Hypergraph  │          │
│  │  Collator   │  │  Collator   │  │  Collator   │          │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘          │
│         │                │                │                  │
│         └────────────────┼────────────────┘                  │
│                          ▼                                   │
│              ┌───────────────────────┐                       │
│              │  UnifiedBatchCollator │                       │
│              │  (sparse block diag)  │                       │
│              └───────────────────────┘                       │
└─────────────────────────────────────────────────────────────┘
```

## Implementation

### Core Collator

```python
import torch
from torch_geometric.data import Batch
from toponetx import SimplicialComplex, CellComplex, CombinatorialComplex
from typing import List, Union, Dict
import scipy.sparse as sp

TopoComplex = Union[SimplicialComplex, CellComplex, CombinatorialComplex]

class TopologicalBatch:
    """Batched topological complexes with sparse adjacency."""
    
    def __init__(
        self,
        complexes: List[TopoComplex],
        features: Dict[int, torch.Tensor],  # rank -> features
        adjacencies: Dict[str, torch.sparse.Tensor],  # "B_1", "L_0", etc.
        batch_indices: Dict[int, torch.Tensor],  # rank -> batch assignment
    ):
        self.complexes = complexes
        self.features = features
        self.adjacencies = adjacencies
        self.batch_indices = batch_indices
        self.batch_size = len(complexes)
    
    def to(self, device: torch.device) -> 'TopologicalBatch':
        return TopologicalBatch(
            complexes=self.complexes,
            features={k: v.to(device) for k, v in self.features.items()},
            adjacencies={k: v.to(device) for k, v in self.adjacencies.items()},
            batch_indices={k: v.to(device) for k, v in self.batch_indices.items()},
        )


def collate_simplicial(
    complexes: List[SimplicialComplex],
    max_rank: int = 2,
) -> TopologicalBatch:
    """Collate simplicial complexes into sparse batched format."""
    
    features = {r: [] for r in range(max_rank + 1)}
    batch_idx = {r: [] for r in range(max_rank + 1)}
    offset = {r: 0 for r in range(max_rank + 1)}
    
    # Boundary matrices per complex
    boundaries = {f"B_{r}": [] for r in range(1, max_rank + 1)}
    laplacians = {f"L_{r}": [] for r in range(max_rank + 1)}
    
    for batch_i, sc in enumerate(complexes):
        for rank in range(max_rank + 1):
            cells = list(sc.skeleton(rank))
            n_cells = len(cells)
            
            # Features (placeholder - use actual if available)
            feat = torch.zeros(n_cells, 1)  # or sc.get_features(rank)
            features[rank].append(feat)
            batch_idx[rank].extend([batch_i] * n_cells)
            
            # Boundary operators
            if rank > 0:
                B = sc.incidence_matrix(rank=rank, signed=True)
                B_shifted = _shift_sparse(B, offset[rank-1], offset[rank])
                boundaries[f"B_{rank}"].append(B_shifted)
            
            # Hodge Laplacian
            L = sc.hodge_laplacian_matrix(rank=rank)
            L_shifted = _shift_sparse(L, offset[rank], offset[rank])
            laplacians[f"L_{rank}"].append(L_shifted)
            
            offset[rank] += n_cells
    
    # Stack features and convert to tensors
    stacked_features = {r: torch.cat(features[r], dim=0) for r in features}
    stacked_batch = {r: torch.tensor(batch_idx[r], dtype=torch.long) for r in batch_idx}
    
    # Block-diagonal sparse matrices
    stacked_adj = {}
    for key, mats in {**boundaries, **laplacians}.items():
        if mats:
            stacked_adj[key] = _block_diag_sparse(mats)
    
    return TopologicalBatch(
        complexes=complexes,
        features=stacked_features,
        adjacencies=stacked_adj,
        batch_indices=stacked_batch,
    )


def _shift_sparse(mat: sp.spmatrix, row_off: int, col_off: int) -> sp.coo_matrix:
    """Shift sparse matrix indices for block-diagonal stacking."""
    coo = mat.tocoo()
    return sp.coo_matrix(
        (coo.data, (coo.row + row_off, coo.col + col_off)),
        shape=(coo.shape[0] + row_off, coo.shape[1] + col_off)
    )


def _block_diag_sparse(mats: List[sp.spmatrix]) -> torch.sparse.Tensor:
    """Create block-diagonal sparse tensor from list of scipy sparse matrices."""
    block = sp.block_diag(mats).tocoo()
    indices = torch.tensor([block.row, block.col], dtype=torch.long)
    values = torch.tensor(block.data, dtype=torch.float32)
    return torch.sparse_coo_tensor(indices, values, block.shape)
```

### PyTorch DataLoader Integration

```python
from torch.utils.data import Dataset, DataLoader

class SimplicialDataset(Dataset):
    """Dataset of simplicial complexes."""
    
    def __init__(self, complexes: List[SimplicialComplex], labels: List[int] = None):
        self.complexes = complexes
        self.labels = labels or [0] * len(complexes)
    
    def __len__(self):
        return len(self.complexes)
    
    def __getitem__(self, idx):
        return self.complexes[idx], self.labels[idx]


def simplicial_collate_fn(batch):
    """Collate function for DataLoader."""
    complexes, labels = zip(*batch)
    topo_batch = collate_simplicial(list(complexes))
    return topo_batch, torch.tensor(labels)


# Usage
dataset = SimplicialDataset(complexes, labels)
loader = DataLoader(
    dataset,
    batch_size=32,
    shuffle=True,
    collate_fn=simplicial_collate_fn,
    num_workers=4,
)

for batch, labels in loader:
    batch = batch.to(device)
    # Forward pass through TopoModelX model
    output = model(batch.features, batch.adjacencies)
```

## GF(3) Integration

```python
def assign_trit_to_cells(complex: SimplicialComplex, seed: int) -> Dict[int, int]:
    """Assign balanced ternary trits to cells for GF(3) conservation."""
    import hashlib
    
    trits = {}
    for rank in range(complex.dim + 1):
        for i, cell in enumerate(complex.skeleton(rank)):
            h = int(hashlib.sha256(f"{seed}:{rank}:{cell}".encode()).hexdigest()[:8], 16)
            trits[(rank, i)] = (h % 3) - 1  # {-1, 0, +1}
    
    # Verify conservation
    total = sum(trits.values())
    assert total % 3 == 0, f"GF(3) violation: sum={total}"
    
    return trits
```

## Path Complexes Extension

From [TopoModelX #230](https://github.com/pyt-team/TopoModelX/issues/230):

```python
class PathComplex:
    """Path complex for directed graph analysis.
    
    A path complex is a simplicial complex where simplices are directed paths.
    Generalizes to allow longer-range dependencies than 1-hop edges.
    """
    
    def __init__(self, graph, max_path_length: int = 3):
        self.graph = graph
        self.max_length = max_path_length
        self._paths = self._enumerate_paths()
    
    def _enumerate_paths(self) -> Dict[int, List[tuple]]:
        """Enumerate all paths up to max_length."""
        from networkx import all_simple_paths
        
        paths = {k: [] for k in range(self.max_length + 1)}
        for source in self.graph.nodes():
            for target in self.graph.nodes():
                for path in all_simple_paths(self.graph, source, target, cutoff=self.max_length):
                    paths[len(path) - 1].append(tuple(path))
        return paths
    
    def boundary_matrix(self, rank: int) -> sp.spmatrix:
        """Compute boundary operator for path complexes."""
        # Boundary of path [v0, v1, ..., vn] is alternating sum of sub-paths
        if rank == 0:
            return sp.csr_matrix((0, len(self._paths[0])))
        
        higher = self._paths[rank]
        lower = self._paths[rank - 1]
        lower_idx = {p: i for i, p in enumerate(lower)}
        
        rows, cols, data = [], [], []
        for i, path in enumerate(higher):
            for j in range(len(path)):
                subpath = path[:j] + path[j+1:]
                if subpath in lower_idx:
                    rows.append(lower_idx[subpath])
                    cols.append(i)
                    data.append((-1) ** j)
        
        return sp.coo_matrix((data, (rows, cols)), shape=(len(lower), len(higher)))
```

## Links

- [TopoModelX](https://github.com/pyt-team/TopoModelX)
- [TopoBenchmarkX](https://github.com/pyt-team/TopoBenchmarkX)
- [TopoX Ecosystem](https://pyt-team.github.io/topox/)
- [Issue #325: Batch training](https://github.com/pyt-team/TopoModelX/issues/325)
- [Issue #243: Dataloaders](https://github.com/pyt-team/TopoModelX/issues/243)

## Commands

```bash
just topo-dataloader-demo    # Run dataloader demonstration
just topo-batch-test         # Test batched complex loading
just topo-path-complex       # Path complex example
```

---

*GF(3) Category: MINUS (Verification) | Addresses production-blocking issues*