---
name: zubyul-gene-networks
description: Gene correlation network analysis bridging WGCNA, pgmpy Bayesian networks, and monad-bayes posterior inference. Load when building gene co-expression modules, learning regulatory network structure, or using HyperNetX hypergraph topology on genomics data.
---

# zubyul-gene-networks

## Origin

Yuliya Zubak (zubyul) built WGCNA pipelines for weighted gene correlation network analysis and processed large genetic sequence data in the Jonikas lab. Repos: `zubyul/WGCNA`, `zubyul/jonikas_lab_data_analysis_misc`.

## WGCNA -> pgmpy Bridge

- Module eigengenes from WGCNA become nodes in a pgmpy Bayesian Network
- Structure learning (Hill Climb / MMHC) discovers regulatory edges
- monad-bayes: `TracedT (WeightedT SamplerIO)` for posterior over network topologies
- Each MCMC step proposes an edge addition/removal, weighted by BIC score

## HyperNetX Hypergraph Topology

- Gene modules are hyperedges (one module = many genes)
- Modularity clustering on the hypergraph partitions functional groups
- Homology mod 2 detects topological holes in the regulatory network
- Contagion dynamics model gene expression cascades

## Bayesian Module Assignment

```haskell
moduleAssignment :: MonadMeasure m => Int -> m (Vector ModuleID)
moduleAssignment nGenes = do
  weights <- dirichlet (replicate nModules 1.0)
  assignments <- replicateM nGenes (categorical weights)
  forM_ (pairs assignments) $ \(i, j) ->
    if sameModule i j
      then factor (Exp (log (correlation i j)))
      else factor (Exp (log (1 - correlation i j)))
  return assignments
```

## Edges

- -> monad-bayes (Bayesian network priors)
- -> pgmpy (BN structure learning)
- -> HyperNetX (hypergraph modules)
- -> zubyul/Nikolova_lab (gene-brain bridge)
