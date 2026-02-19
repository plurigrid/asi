---
name: zubyul-gene-networks
description: Gene correlation network analysis bridging WGCNA, pgmpy Bayesian networks, and monad-bayes posterior inference. Connects zubyul's genomics background to the plurigrid interactome via HyperNetX hypergraph topology.
---

# zubyul-gene-networks Skill

> *Scale-free gene modules as Bayesian hypergraphs*

## Origin: zubyul/WGCNA + zubyul/jonikas_lab_data_analysis_misc

Yuliya Zubak (zubyul) built WGCNA pipelines for weighted gene correlation
network analysis and processed large genetic sequence data in the Jonikas lab.

## What's Possible

### 1. WGCNA -> pgmpy Bridge
- Module eigengenes from WGCNA become nodes in a pgmpy Bayesian Network
- Structure learning (Hill Climb / MMHC) discovers regulatory edges
- monad-bayes: `TracedT (WeightedT SamplerIO)` for posterior over network topologies
- Each MCMC step proposes an edge addition/removal, weighted by BIC score

### 2. HyperNetX Hypergraph Topology
- Gene modules are hyperedges (one module = many genes)
- Modularity clustering on the hypergraph partitions functional groups
- Homology mod 2 detects topological holes in the regulatory network
- Contagion dynamics model gene expression cascades

### 3. monad-bayes Integration
```haskell
-- Posterior over WGCNA module assignments
moduleAssignment :: MonadMeasure m => Int -> m (Vector ModuleID)
moduleAssignment nGenes = do
  -- Prior: Dirichlet-Multinomial over module labels
  weights <- dirichlet (replicate nModules 1.0)
  assignments <- replicateM nGenes (categorical weights)
  -- Likelihood: within-module correlation > between-module
  forM_ (pairs assignments) $ \(i, j) ->
    if sameModule i j
      then factor (Exp (log (correlation i j)))
      else factor (Exp (log (1 - correlation i j)))
  return assignments
```

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
