---
name: vertex-protein-bisimulation
description: >
  Protein folding as compositional game on Vertex AI. GameOpt combinatorial
  Bayesian optimization over residue positions, bisimulation on conformational
  trajectories, monad-bayes posterior over folding pathways. Use when applying
  game-theoretic optimization to protein design, checking bisimulation
  equivalence of folding trajectories, or running AlphaFold/ESMFold batch
  prediction on Vertex AI.
---

# vertex-protein-bisimulation

> *Folding funnel = payoff landscape. Minimal frustration = Nash equilibrium.*

## Architecture

```
Basin-Hedges (ParaLens 6-wire)
  |
  +-- GameOpt layer (Bal, Sessa, Mutny, Krause 2024)
  |     Residue positions = players
  |     Amino acid identities = strategies
  |     Upper confidence bound equilibria guide search
  |     Counterfactual gating prunes combinatorial space
  |
  +-- Vertex AI Pipeline (compute backend)
  |     AlphaFold v2 batch: KFP pipeline, 3 phases
  |       CPU (MSA) -> GPU (predict) -> GPU (relax)
  |     ESMFold: single-seq, no MSA, 10-30x faster
  |       HuggingFace: facebook/esmfold_v1
  |     Batch prediction: 50% cost discount, 24hr
  |
  +-- Bisimulation on Folding
        Two trajectories bisimilar iff same native state
        Despite different intermediate conformations
        Stochastic process algebra on Markov state models
        CellValue lattice: Nothing=unfolded, Value=native,
          Contradiction=misfolded aggregate
```

## monad-bayes Integration

```haskell
-- Posterior over folding pathways
foldingPathway :: MonadMeasure m => Sequence -> m Structure
foldingPathway seq = do
  angles <- replicateM (length seq) $ do
    phi <- uniform (-pi) pi
    psi <- uniform (-pi) pi
    return (phi, psi)
  let energy = forceField seq angles
  factor (Exp (negate energy / kT))
  return (buildStructure seq angles)

-- GameOpt: combinatorial optimization as open game
proteinGame :: OpenGame Stochastic [AminoAcid] Energy
proteinGame = sequentialCompose residueGames
  where residueGames = map residueChoice [1..nPositions]
        residueChoice i = decision "residue_i" aminoAcids ucbPayoff
```

## Key Papers

- GameOpt (2024): arxiv.org/abs/2409.18582
- Bayesian Open Games (Bolt, Hedges, Zahn 2019): arxiv.org/abs/1910.03656
- MELD Bayesian protein (PNAS): doi.org/10.1073/pnas.1506788112
- AMix-1 Bayesian Flow Networks (2025): protein foundation model
