---
name: zubyul-gene-networks <<<<<<< HEAD
description: Gene correlation network analysis bridging WGCNA, pgmpy Bayesian networks, and monad-bayes posterior inference. Connects zubyul's genomics background to the plurigrid interactome via HyperNetX hypergraph topology.
---

# zubyul-gene-networks Skill

> *Scale-free gene modules as Bayesian hypergraphs*

## Origin: zubyul/WGCNA + zubyul/jonikas_lab_data_analysis_misc

Yuliya Zubak (zubyul) built WGCNA pipelines for weighted gene correlation
network analysis and processed large genetic sequence data in the Jonikas lab.

## What's Possible

### 1. WGCNA -> pgmpy Bridge
=======
description: Gene correlation network analysis bridging WGCNA, pgmpy Bayesian networks, and monad-bayes posterior inference. Load when building gene co-expression modules, learning regulatory network structure, or using HyperNetX hypergraph topology on genomics data.
---

# zubyul-gene-networks

## Origin

Yuliya Zubak (zubyul) built WGCNA pipelines for weighted gene correlation network analysis and processed large genetic sequence data in the Jonikas lab. Repos: `zubyul/WGCNA`, `zubyul/jonikas_lab_data_analysis_misc`.

## WGCNA -> pgmpy Bridge

>>>>>>> origin/main
- Module eigengenes from WGCNA become nodes in a pgmpy Bayesian Network
- Structure learning (Hill Climb / MMHC) discovers regulatory edges
- monad-bayes: `TracedT (WeightedT SamplerIO)` for posterior over network topologies
- Each MCMC step proposes an edge addition/removal, weighted by BIC score

<<<<<<< HEAD
### 2. HyperNetX Hypergraph Topology
=======
## HyperNetX Hypergraph Topology

>>>>>>> origin/main
- Gene modules are hyperedges (one module = many genes)
- Modularity clustering on the hypergraph partitions functional groups
- Homology mod 2 detects topological holes in the regulatory network
- Contagion dynamics model gene expression cascades

<<<<<<< HEAD
### 3. monad-bayes Integration
```haskell
-- Posterior over WGCNA module assignments
moduleAssignment :: MonadMeasure m => Int -> m (Vector ModuleID)
moduleAssignment nGenes = do
  -- Prior: Dirichlet-Multinomial over module labels
  weights <- dirichlet (replicate nModules 1.0)
  assignments <- replicateM nGenes (categorical weights)
  -- Likelihood: within-module correlation > between-module
=======
## Bayesian Module Assignment

```haskell
moduleAssignment :: MonadMeasure m => Int -> m (Vector ModuleID)
moduleAssignment nGenes = do
  weights <- dirichlet (replicate nModules 1.0)
  assignments <- replicateM nGenes (categorical weights)
>>>>>>> origin/main
  forM_ (pairs assignments) $ \(i, j) ->
    if sameModule i j
      then factor (Exp (log (correlation i j)))
      else factor (Exp (log (1 - correlation i j)))
  return assignments
```

<<<<<<< HEAD
### 4. GF(3) Trit Classification
| Component | Trit | Role |
|-----------|------|------|
| WGCNA eigengenes | +1 | Generation (data -> modules) |
| pgmpy BN learning | 0 | Coordination (structure) |
| monad-bayes posterior | -1 | Validation (model selection) |

Conservation: +1 + 0 + (-1) = 0

## Edges in Interactome TUI
- -> monad-bayes (w=0.70, Bayesian network priors)
- -> pgmpy (w=0.80, BN structure learning)
- -> HyperNetX (w=0.85, hypergraph modules)
- -> zubyul/Nikolova_lab (w=0.90, gene-brain bridge)

## Trit: 0 (ERGODIC - bridges genomics to interactome)
=======
## Concrete Affordances

### Clone Upstream Repositories

```bash
# WGCNA analysis pipeline
git clone https://github.com/zubyul/WGCNA.git /Users/alice/v/zubyul-wgcna

# Jonikas lab data processing
git clone https://github.com/zubyul/jonikas_lab_data_analysis_misc.git /Users/alice/v/zubyul-jonikas
```

### Bayesian Network Structure Learning from WGCNA Eigengenes (pgmpy)

Learn the regulatory DAG over module eigengenes discovered by WGCNA:

```python
# pip install pgmpy pandas numpy
import pandas as pd
import numpy as np
from pgmpy.estimators import HillClimbSearch, BicScore
from pgmpy.models import BayesianNetwork
from pgmpy.estimators import MaximumLikelihoodEstimator

np.random.seed(42)

# Simulated WGCNA module eigengenes (replace with real eigengene matrix from R)
# Columns = module colors (WGCNA convention), rows = samples
n_samples = 200
eigengenes = pd.DataFrame({
    'ME_blue':   np.random.randn(n_samples),
    'ME_brown':  np.random.randn(n_samples),
    'ME_turquoise': np.random.randn(n_samples),
    'ME_green':  np.random.randn(n_samples),
    'ME_yellow': np.random.randn(n_samples),
})
# Inject causal structure: blue -> brown, turquoise -> green, blue -> yellow
eigengenes['ME_brown'] += 0.6 * eigengenes['ME_blue']
eigengenes['ME_green'] += 0.5 * eigengenes['ME_turquoise']
eigengenes['ME_yellow'] += 0.4 * eigengenes['ME_blue'] + 0.3 * eigengenes['ME_turquoise']

# Discretize for BN (or use linear Gaussian BN)
discretized = eigengenes.apply(lambda col: pd.cut(col, bins=3, labels=['low','mid','high']))

# Hill Climb structure learning with BIC scoring
hc = HillClimbSearch(discretized)
best_model = hc.estimate(scoring_method=BicScore(discretized), max_indegree=3)

print("Learned DAG edges (regulatory relationships):")
for edge in best_model.edges():
    print(f"  {edge[0]} -> {edge[1]}")

# Fit parameters
bn = BayesianNetwork(best_model.edges())
bn.fit(discretized, estimator=MaximumLikelihoodEstimator)
print(f"\nNodes: {bn.nodes()}")
print(f"Edges: {bn.edges()}")
```

### Gene Module Hypergraph with HyperNetX

Construct a hypergraph where each WGCNA module is a hyperedge containing its member genes:

```python
# pip install hypernetx matplotlib
import hypernetx as hnx
import matplotlib.pyplot as plt

# Gene-to-module assignments from WGCNA (replace with real output)
# Each module (hyperedge) contains multiple genes (nodes)
module_membership = {
    'blue':      ['BDNF', 'SLC6A4', 'HTR2A', 'FKBP5', 'NR3C1'],
    'brown':     ['COMT', 'MAOA', 'DRD2', 'DRD4', 'SLC6A3'],
    'turquoise': ['DISC1', 'NRG1', 'DTNBP1', 'CACNA1C', 'ANK3', 'TCF4'],
    'green':     ['NTRK2', 'CREB1', 'ARC', 'HOMER1'],
    'yellow':    ['SLC6A4', 'TPH2', 'MAOA', 'HTR1A'],  # note: SLC6A4, MAOA overlap
}

H = hnx.Hypergraph(module_membership)

# Basic topology
print(f"Nodes (genes): {H.number_of_nodes()}")
print(f"Hyperedges (modules): {H.number_of_edges()}")

# Genes shared across modules (hub genes / overlapping membership)
for node in H.nodes():
    memberships = H.nodes.memberships[node]
    if len(memberships) > 1:
        print(f"  Hub gene {node} in modules: {memberships}")

# Compute s-adjacency: two modules are s-adjacent if they share >= s genes
for s in [1, 2]:
    adj = H.adjacency_matrix(s=s)
    print(f"\n{s}-adjacency matrix (modules sharing >= {s} genes):")
    print(adj.todense())

# Visualize
hnx.drawing.draw(H, with_node_labels=True, with_edge_labels=True)
plt.title("WGCNA Gene Module Hypergraph")
plt.savefig("/tmp/gene_module_hypergraph.png", dpi=150, bbox_inches='tight')
print("Hypergraph saved to /tmp/gene_module_hypergraph.png")
```

### Load WGCNA Eigengenes from R Output

Bridge R WGCNA output into Python:

```python
# After running WGCNA in R, export eigengenes:
#   write.csv(MEs, "module_eigengenes.csv", row.names=TRUE)
import pandas as pd

eigengenes = pd.read_csv("/Users/alice/v/zubyul-wgcna/output/module_eigengenes.csv", index_col=0)
print(f"Loaded {eigengenes.shape[1]} module eigengenes for {eigengenes.shape[0]} samples")
print(eigengenes.head())
```

## Edges

- -> monad-bayes (Bayesian network priors)
- -> pgmpy (BN structure learning)
- -> HyperNetX (hypergraph modules)
- -> zubyul/Nikolova_lab (gene-brain bridge)
>>>>>>> origin/main
