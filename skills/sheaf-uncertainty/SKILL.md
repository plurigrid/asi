---
name: sheaf-uncertainty
description: Bayesian sheaf neural networks for uncertainty quantification. Sheaf
  Laplacian consensus with GF(3) confidence intervals.
source: arXiv:2410.09590 + TheMesocarp/koho + GitHub research
license: MIT
gf3_category: MINUS
---

# Sheaf Uncertainty Skill

> **Based on**: [Bayesian Sheaf Neural Networks (arXiv:2410.09590)](https://arxiv.org/abs/2410.09590) and [koho](https://github.com/TheMesocarp/koho)

## What Are Sheaf Neural Networks?

Sheaf neural networks generalize GNNs by learning **local-to-global consistency** via sheaf structures:

```
Traditional GNN:
  Node features → Aggregate neighbors → Update

Sheaf NN:
  Node features → Transform via restriction maps → 
  Measure consistency (Laplacian) → Update to minimize discrepancy
```

The **sheaf Laplacian** measures how much local data disagrees across edges:

$$L_{\mathcal{F}} = B^T D B$$

where:
- $B$ = signed incidence matrix
- $D$ = block-diagonal of restriction maps $\mathcal{F}(v \leftarrow e)$

## Bayesian Extension

Add uncertainty quantification by treating restriction maps as random variables:

```python
import torch
import torch.nn as nn
from torch.distributions import Normal, kl_divergence

class BayesianRestrictionMap(nn.Module):
    """Restriction map with learned uncertainty."""
    
    def __init__(self, stalk_dim: int, edge_dim: int):
        super().__init__()
        self.stalk_dim = stalk_dim
        self.edge_dim = edge_dim
        
        # Mean and log-variance of restriction map weights
        self.W_mu = nn.Parameter(torch.randn(stalk_dim, edge_dim) * 0.1)
        self.W_logvar = nn.Parameter(torch.zeros(stalk_dim, edge_dim) - 2)
    
    def forward(self, x: torch.Tensor, sample: bool = True) -> torch.Tensor:
        """Apply restriction map with optional sampling."""
        if sample and self.training:
            std = torch.exp(0.5 * self.W_logvar)
            eps = torch.randn_like(std)
            W = self.W_mu + std * eps
        else:
            W = self.W_mu
        
        return x @ W
    
    def kl_divergence(self, prior_std: float = 1.0) -> torch.Tensor:
        """KL divergence from prior N(0, prior_std^2)."""
        prior = Normal(0, prior_std)
        posterior = Normal(self.W_mu, torch.exp(0.5 * self.W_logvar))
        return kl_divergence(posterior, prior).sum()


class BayesianSheafConv(nn.Module):
    """Bayesian sheaf convolution layer."""
    
    def __init__(
        self,
        in_channels: int,
        out_channels: int,
        stalk_dim: int,
        num_edge_types: int = 1,
    ):
        super().__init__()
        self.stalk_dim = stalk_dim
        
        # Learnable restriction maps (source and target per edge type)
        self.restrict_src = nn.ModuleList([
            BayesianRestrictionMap(in_channels, stalk_dim)
            for _ in range(num_edge_types)
        ])
        self.restrict_tgt = nn.ModuleList([
            BayesianRestrictionMap(in_channels, stalk_dim)
            for _ in range(num_edge_types)
        ])
        
        # Output projection
        self.project = nn.Linear(stalk_dim, out_channels)
    
    def forward(
        self,
        x: torch.Tensor,
        edge_index: torch.Tensor,
        edge_type: torch.Tensor = None,
    ) -> tuple[torch.Tensor, torch.Tensor]:
        """
        Returns:
            out: Node features after sheaf diffusion
            uncertainty: Per-node uncertainty estimate
        """
        src, tgt = edge_index
        
        if edge_type is None:
            edge_type = torch.zeros(edge_index.size(1), dtype=torch.long)
        
        # Apply restriction maps
        x_src_restricted = torch.zeros(edge_index.size(1), self.stalk_dim)
        x_tgt_restricted = torch.zeros(edge_index.size(1), self.stalk_dim)
        
        for et in edge_type.unique():
            mask = edge_type == et
            x_src_restricted[mask] = self.restrict_src[et](x[src[mask]])
            x_tgt_restricted[mask] = self.restrict_tgt[et](x[tgt[mask]])
        
        # Sheaf Laplacian diffusion: minimize ||F(s←e)(x_s) - F(t←e)(x_t)||²
        discrepancy = x_src_restricted - x_tgt_restricted
        
        # Aggregate discrepancy back to nodes
        node_discrepancy = torch.zeros(x.size(0), self.stalk_dim)
        node_discrepancy.index_add_(0, src, discrepancy)
        node_discrepancy.index_add_(0, tgt, -discrepancy)
        
        # Update: move toward consistency
        out = self.project(x[:, :self.stalk_dim] - 0.5 * node_discrepancy)
        
        # Uncertainty = magnitude of disagreement
        uncertainty = torch.norm(node_discrepancy, dim=1)
        
        return out, uncertainty
    
    def kl_loss(self) -> torch.Tensor:
        """Total KL divergence for all restriction maps."""
        kl = sum(rm.kl_divergence() for rm in self.restrict_src)
        kl += sum(rm.kl_divergence() for rm in self.restrict_tgt)
        return kl
```

## GF(3) Confidence Intervals

Map uncertainty to balanced ternary confidence:

```python
def uncertainty_to_gf3_confidence(
    uncertainty: torch.Tensor,
    thresholds: tuple[float, float] = (0.3, 0.7),
) -> torch.Tensor:
    """
    Map uncertainty to GF(3) confidence trits.
    
    - PLUS (+1): Low uncertainty → High confidence
    - ZERO (0): Medium uncertainty → Neutral confidence
    - MINUS (-1): High uncertainty → Low confidence
    
    Returns balanced ternary tensor.
    """
    low_thresh, high_thresh = thresholds
    
    # Normalize uncertainty to [0, 1]
    u_norm = (uncertainty - uncertainty.min()) / (uncertainty.max() - uncertainty.min() + 1e-8)
    
    # Map to trits
    trits = torch.zeros_like(u_norm, dtype=torch.long)
    trits[u_norm < low_thresh] = 1      # PLUS: confident
    trits[u_norm > high_thresh] = -1    # MINUS: uncertain
    # ZERO: in between
    
    return trits


def verify_gf3_conservation(trits: torch.Tensor) -> bool:
    """Check that sum of trits ≡ 0 (mod 3)."""
    return trits.sum().item() % 3 == 0


def balance_trits(trits: torch.Tensor) -> torch.Tensor:
    """Adjust trits to satisfy GF(3) conservation."""
    remainder = trits.sum().item() % 3
    if remainder == 0:
        return trits
    
    # Find nodes to adjust (prefer ZERO nodes)
    zero_mask = trits == 0
    if zero_mask.sum() >= abs(remainder):
        # Adjust ZERO nodes
        adjust_indices = zero_mask.nonzero()[:abs(remainder)]
        adjustment = -1 if remainder == 1 else 1
        trits[adjust_indices] = adjustment
    
    return trits
```

## Sheaf Cohomology for Obstruction Detection

```python
def compute_sheaf_cohomology(
    node_features: torch.Tensor,
    edge_index: torch.Tensor,
    restriction_maps: dict,
) -> dict:
    """
    Compute sheaf cohomology groups to detect coordination obstructions.
    
    H⁰ = global sections (consistent assignments)
    H¹ = obstructions to patching (coordination bottlenecks)
    """
    src, tgt = edge_index
    n_nodes = node_features.size(0)
    n_edges = edge_index.size(1)
    stalk_dim = node_features.size(1)
    
    # Build coboundary operator δ⁰: C⁰ → C¹
    # (δ⁰f)(e) = F(t←e)(f_t) - F(s←e)(f_s)
    delta_0 = torch.zeros(n_edges * stalk_dim, n_nodes * stalk_dim)
    
    for i, (s, t) in enumerate(edge_index.T):
        F_src = restriction_maps.get((s.item(), i), torch.eye(stalk_dim))
        F_tgt = restriction_maps.get((t.item(), i), torch.eye(stalk_dim))
        
        delta_0[i*stalk_dim:(i+1)*stalk_dim, s*stalk_dim:(s+1)*stalk_dim] = -F_src
        delta_0[i*stalk_dim:(i+1)*stalk_dim, t*stalk_dim:(t+1)*stalk_dim] = F_tgt
    
    # H⁰ = ker(δ⁰) = global sections
    _, s, vh = torch.linalg.svd(delta_0)
    kernel_dim = (s < 1e-6).sum().item()
    h0_basis = vh[-kernel_dim:] if kernel_dim > 0 else None
    
    # H¹ = coker(δ⁰) ≈ obstructions
    u, s, _ = torch.linalg.svd(delta_0.T)
    cokernel_dim = (s < 1e-6).sum().item()
    h1_basis = u[:, -cokernel_dim:] if cokernel_dim > 0 else None
    
    return {
        'h0_dim': kernel_dim,  # Dimension of global sections
        'h1_dim': cokernel_dim,  # Dimension of obstructions
        'h0_basis': h0_basis,
        'h1_basis': h1_basis,
        'has_obstructions': cokernel_dim > 0,
    }
```

## Koho Benchmark Integration

From [koho](https://github.com/TheMesocarp/koho):

```python
# Benchmark sheaf NNs on heterophilic graphs
KOHO_DATASETS = [
    'cornell', 'texas', 'wisconsin',  # WebKB (heterophilic)
    'chameleon', 'squirrel',          # Wikipedia (heterophilic)
    'actor',                           # Film industry
]

def run_koho_benchmark(model, dataset_name: str):
    """Run koho-style benchmark comparing SheafNN to GNN baselines."""
    from torch_geometric.datasets import WebKB, WikipediaNetwork, Actor
    
    # Load dataset
    if dataset_name in ['cornell', 'texas', 'wisconsin']:
        dataset = WebKB(root='/tmp', name=dataset_name)
    elif dataset_name in ['chameleon', 'squirrel']:
        dataset = WikipediaNetwork(root='/tmp', name=dataset_name)
    else:
        dataset = Actor(root='/tmp')
    
    data = dataset[0]
    
    # Train/val/test split
    # ... standard evaluation loop ...
    
    return {
        'accuracy': acc,
        'uncertainty_calibration': calibration_score,
        'gf3_conservation': verify_gf3_conservation(model.get_trits()),
    }
```

## Links

- [Bayesian Sheaf Neural Networks (arXiv:2410.09590)](https://arxiv.org/abs/2410.09590)
- [koho benchmark](https://github.com/TheMesocarp/koho)
- [Sheaf Neural Networks (arXiv:2012.06333)](https://arxiv.org/abs/2012.06333)
- [Neural Sheaf Diffusion (arXiv:2202.04579)](https://arxiv.org/abs/2202.04579)

## Commands

```bash
just sheaf-uncertainty-demo   # Bayesian sheaf NN demonstration
just sheaf-cohomology         # Compute cohomology obstructions
just sheaf-gf3-confidence     # GF(3) confidence intervals
just koho-benchmark           # Run koho heterophilic benchmark
```

---

*GF(3) Category: MINUS (Verification) | Uncertainty quantification via sheaf structure*