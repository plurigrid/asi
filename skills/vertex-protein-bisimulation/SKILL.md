---
name: vertex-protein-bisimulation
<<<<<<< HEAD
description: Protein folding as compositional game on Vertex AI. GameOpt combinatorial Bayesian optimization over residue positions, bisimulation on conformational trajectories, monad-bayes posterior over folding pathways.
---

# vertex-protein-bisimulation Skill
=======
description: >
  Protein folding as compositional game on Vertex AI. GameOpt combinatorial
  Bayesian optimization over residue positions, bisimulation on conformational
  trajectories, monad-bayes posterior over folding pathways. Use when applying
  game-theoretic optimization to protein design, checking bisimulation
  equivalence of folding trajectories, or running AlphaFold/ESMFold batch
  prediction on Vertex AI.
---

# vertex-protein-bisimulation
>>>>>>> origin/main

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
<<<<<<< HEAD
  -- Prior: Ramachandran angles per residue
=======
>>>>>>> origin/main
  angles <- replicateM (length seq) $ do
    phi <- uniform (-pi) pi
    psi <- uniform (-pi) pi
    return (phi, psi)
<<<<<<< HEAD
  -- Energy function as likelihood
  let energy = forceField seq angles
  factor (Exp (negate energy / kT))
  -- Return structure
=======
  let energy = forceField seq angles
  factor (Exp (negate energy / kT))
>>>>>>> origin/main
  return (buildStructure seq angles)

-- GameOpt: combinatorial optimization as open game
proteinGame :: OpenGame Stochastic [AminoAcid] Energy
proteinGame = sequentialCompose residueGames
  where residueGames = map residueChoice [1..nPositions]
        residueChoice i = decision "residue_i" aminoAcids ucbPayoff
```

<<<<<<< HEAD
## Key Papers
=======
## Concrete Affordances

### AlphaFold Batch Workflow on Vertex AI

Run the 3-phase AlphaFold pipeline (MSA on CPU, prediction on GPU, relaxation on GPU) via Vertex AI Pipelines. See also: `vertex-ai-protein-interleave` skill for full gcloud project setup.

```bash
# Prerequisites:
#   gcloud auth login
#   gcloud config set project YOUR_PROJECT_ID
#   gcloud services enable aiplatform.googleapis.com lifesciences.googleapis.com

# 1. Build the AlphaFold container (one-time)
gcloud builds submit \
  --tag gcr.io/${GOOGLE_CLOUD_PROJECT}/alphafold-batch:latest \
  --timeout=3600s \
  /Users/alice/v/asi/skills/vertex-ai-protein-interleave/docker/

# 2. Submit a batch prediction pipeline
#    Input: FASTA file in GCS; Output: PDB structures in GCS
gcloud ai custom-jobs create \
  --region=us-central1 \
  --display-name="alphafold-batch-$(date +%Y%m%d-%H%M%S)" \
  --worker-pool-spec="\
machine-type=n1-standard-8,\
accelerator-type=NVIDIA_TESLA_A100,\
accelerator-count=1,\
replica-count=1,\
container-image-uri=gcr.io/${GOOGLE_CLOUD_PROJECT}/alphafold-batch:latest" \
  --args="--fasta_paths=gs://${GOOGLE_CLOUD_PROJECT}-alphafold/input/sequences.fasta,\
--output_dir=gs://${GOOGLE_CLOUD_PROJECT}-alphafold/output/,\
--model_preset=monomer,\
--db_preset=reduced_dbs,\
--max_template_date=2026-03-01"

# 3. Monitor the job
gcloud ai custom-jobs list --region=us-central1 --filter="displayName~alphafold-batch" --limit=5
gcloud ai custom-jobs describe JOB_ID --region=us-central1
```

### ESMFold Single-Sequence Prediction (Python)

Faster alternative when MSA is unnecessary:

```python
# pip install torch transformers
from transformers import EsmForProteinFolding, AutoTokenizer
import torch

tokenizer = AutoTokenizer.from_pretrained("facebook/esmfold_v1")
model = EsmForProteinFolding.from_pretrained("facebook/esmfold_v1")
model = model.eval()

sequence = "MKTVRQERLKSIVRILERSKEPVSGAQLAEELSVSRQVIVQDIAYLRSLGYNIVATPRGYVLAGG"
inputs = tokenizer([sequence], return_tensors="pt", add_special_tokens=False)

with torch.no_grad():
    output = model(**inputs)

# Extract pLDDT confidence and PDB string
plddt = output["plddt"].mean().item()
pdb_str = model.output_to_pdb(output)[0]
print(f"Mean pLDDT: {plddt:.1f}")
with open("/tmp/predicted.pdb", "w") as f:
    f.write(pdb_str)
print("Structure written to /tmp/predicted.pdb")
```

### GameOpt over Residue Positions (Python)

Combinatorial Bayesian optimization treating residue positions as players in a game. Uses `scipy.optimize` for the upper confidence bound acquisition:

```python
# pip install scipy numpy
import numpy as np
from scipy.optimize import minimize

# 20 standard amino acids, N mutable positions
AMINO_ACIDS = list("ACDEFGHIKLMNPQRSTVWY")
N_POSITIONS = 5

# Simulated energy function (replace with AlphaFold/ESMFold pLDDT call)
def energy_fn(encoding: np.ndarray) -> float:
    """Negative pLDDT proxy. encoding: (N_POSITIONS,) floats in [0, 19]."""
    rounded = np.round(encoding).astype(int) % 20
    # Placeholder: pairwise contact energy
    return sum(abs(rounded[i] - rounded[i+1]) * 0.1 for i in range(len(rounded)-1))

# UCB acquisition: f(x) - kappa * sigma(x)
# In GameOpt each position is a "player" choosing an amino acid
def ucb_acquisition(x, kappa=2.0, gp_mean=None, gp_std=None):
    """Upper confidence bound for game-theoretic BO."""
    mu = gp_mean(x) if gp_mean else energy_fn(x)
    sigma = gp_std(x) if gp_std else 0.5  # prior uncertainty
    return mu - kappa * sigma

# Per-player (per-residue) best response via scipy
def gameopt_step(current: np.ndarray, position: int) -> int:
    """Find best amino acid at `position` holding others fixed (Nash best response)."""
    best_aa, best_val = 0, float('inf')
    for aa_idx in range(20):
        candidate = current.copy()
        candidate[position] = aa_idx
        val = ucb_acquisition(candidate)
        if val < best_val:
            best_val = val
            best_aa = aa_idx
    return best_aa

# Iterative best-response loop (converges to Nash equilibrium)
state = np.random.randint(0, 20, size=N_POSITIONS).astype(float)
for iteration in range(50):
    for pos in range(N_POSITIONS):
        state[pos] = gameopt_step(state, pos)
    e = energy_fn(state)
    if iteration % 10 == 0:
        seq = ''.join(AMINO_ACIDS[int(s) % 20] for s in state)
        print(f"Iter {iteration}: sequence={seq}  energy={e:.4f}")

final_seq = ''.join(AMINO_ACIDS[int(s) % 20] for s in state)
print(f"GameOpt result: {final_seq}  energy={energy_fn(state):.4f}")
```

### Bisimulation Check on Folding Trajectories (Python)

Check whether two MD folding trajectories reach bisimilar native states:

```python
# pip install mdtraj numpy
import mdtraj as md
import numpy as np

def rmsd_bisimulation(traj_a_path: str, traj_b_path: str, threshold_nm: float = 0.3) -> dict:
    """
    Two trajectories are bisimilar iff their final frames have RMSD < threshold.
    This implements the stochastic process algebra check from the architecture doc:
      bisimilar <=> same native state despite different intermediates.
    """
    traj_a = md.load(traj_a_path)
    traj_b = md.load(traj_b_path)

    # Align final frames
    final_a = traj_a[-1]
    final_b = traj_b[-1]
    rmsd = md.rmsd(final_b, final_a)[0]

    return {
        "bisimilar": rmsd < threshold_nm,
        "rmsd_nm": float(rmsd),
        "threshold_nm": threshold_nm,
        "traj_a_frames": traj_a.n_frames,
        "traj_b_frames": traj_b.n_frames,
    }

# Usage:
# result = rmsd_bisimulation("fold_run1.xtc", "fold_run2.xtc", threshold_nm=0.3)
# print(result)
```

## Key Papers

>>>>>>> origin/main
- GameOpt (2024): arxiv.org/abs/2409.18582
- Bayesian Open Games (Bolt, Hedges, Zahn 2019): arxiv.org/abs/1910.03656
- MELD Bayesian protein (PNAS): doi.org/10.1073/pnas.1506788112
- AMix-1 Bayesian Flow Networks (2025): protein foundation model
<<<<<<< HEAD

## GF(3) Trit Classification
| Component | Trit | Role |
|-----------|------|------|
| ESMFold/AlphaFold prediction | +1 | Generation |
| GameOpt equilibrium search | 0 | Coordination |
| Bisimulation equivalence check | -1 | Validation |

Conservation: +1 + 0 + (-1) = 0

## Edges in Interactome TUI
- -> monad-bayes (w=0.65, Bayesian structure posterior)
- -> geomstats (w=0.60, protein manifold geometry)
- -> bisimulation-game (w=0.90, conformational bisimulation)
- -> zubyul/Nikolova_lab (w=0.70, transcription factor bridge)

## Trit: 0 (ERGODIC)
=======
>>>>>>> origin/main
