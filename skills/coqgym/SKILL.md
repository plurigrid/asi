# CoqGym

Machine learning environment for automated theorem proving with Coq.

## Overview

[CoqGym](https://github.com/princeton-vl/CoqGym) is a learning environment for theorem proving with the Coq proof assistant. It provides:

- **71K human-written proofs** from 123 Coq projects
- **ASTactic** - neural theorem prover using proof state ASTs
- **CoqHammer integration** for automated reasoning
- **Benchmark** for evaluating ML-based provers

Paper: [arXiv:1905.09381](https://arxiv.org/abs/1905.09381)

## Installation

```bash
# Clone repository
git clone https://github.com/princeton-vl/CoqGym
cd CoqGym

# Install dependencies
pip install -r requirements.txt

# Install Coq 8.9.1
opam switch create coq891 4.07.1
opam install coq.8.9.1

# Build CoqGym
python setup.py build
```

## Dataset Structure

```
CoqGym/
├── coq_projects/     # 123 Coq projects
├── data/             # Extracted proof data
│   ├── *.json        # Proof states and tactics
│   └── sexp_cache/   # S-expression cache
├── ASTactic/         # Neural prover
└── coqhammer/        # Hammer integration
```

## Proof State Representation

Each proof state contains:
- **Goals**: Current proof obligations
- **Local context**: Hypotheses in scope
- **Global context**: Available lemmas/definitions
- **Tactic history**: Previous tactics applied

```python
{
    "goals": [...],
    "local_context": [...],
    "tactic": "intros n.",
    "proof_tree": {...}
}
```

## ASTactic Model

Neural network that predicts tactics from proof state ASTs:

```python
from astactic import ASTactic

model = ASTactic.load("models/astactic.pt")
tactic = model.predict(proof_state)
```

Architecture:
- TreeLSTM encoder for AST structure
- Attention over local/global context
- Tactic decoder with copy mechanism

## Training

```bash
# Extract proofs
python extract_proofs.py --project mathcomp

# Train ASTactic
python train.py \
    --data data/train.json \
    --model astactic \
    --epochs 100
```

## Evaluation

```bash
# Evaluate on test set
python evaluate.py \
    --model models/astactic.pt \
    --data data/test.json \
    --timeout 600
```

Metrics:
- **Proof success rate**: % of theorems proved
- **Tactic accuracy**: Top-k tactic prediction
- **Proof length**: Steps vs human proofs

## CoqHammer Integration

Combines ML predictions with automated reasoning:

```coq
(* In Coq *)
Require Import Hammer.

Lemma example : forall n, n + 0 = n.
Proof.
  hammer.  (* Calls external ATPs *)
Qed.
```

## Integration with Gay.jl Verification

Use CoqGym to learn proof strategies for Gay.jl properties:

1. **Extract** proofs from similar PRNG verification projects
2. **Train** on SplitMix64-style proofs
3. **Apply** learned tactics to new Gay.jl lemmas

```python
# Find similar proofs
similar = coqgym.search(
    query="deterministic hash function",
    projects=["compcert", "flocq"]
)
```

## GF(3) Trit

| Role | Trit | Description |
|------|------|-------------|
| Learner | -1 | Extract patterns from proofs |
| Predictor | 0 | Tactic prediction (ergodic) |
| Prover | +1 | Generate complete proofs |

## Key Papers

- [Learning to Prove Theorems via Interacting with Proof Assistants](https://arxiv.org/abs/1905.09381)
- [Graph Neural Networks for Theorem Proving](https://arxiv.org/abs/2003.04883)
- [Automated Theorem Proving with GNNs](https://medium.com/stanford-cs224w/automated-theorem-proving-with-graph-neural-networks-49c091024f81)

## Resources

- [GitHub](https://github.com/princeton-vl/CoqGym)
- [Princeton Vision Lab](https://www.cs.princeton.edu/~kaiyang/)
- [Coq Documentation](https://coq.inria.fr/documentation)

## Related Skills

- `coq-of-rust` - Rust to Coq translation
- `narya-proofs` - Higher observational type theory
- `proofgeneral-narya` - Proof assistant integration
- `forward-forward-learning` - Local learning without backprop


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
