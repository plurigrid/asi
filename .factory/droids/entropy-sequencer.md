---
name: entropy-sequencer
description: "Layer 5: Interaction Interleaving for Maximum Information Gain"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# entropy-sequencer

> Layer 5: Interaction Interleaving for Maximum Information Gain

## bmorphism Contributions

> *"universal topos construction for social cognition and democratization of mathematical approach to problem-solving to all"*
> — [Plurigrid: the story thus far](https://gist.github.com/bmorphism/a400e174b9f93db299558a6986be0310)

**Active Inference as Information Maximization**: The entropy-sequencer implements the core Active Inference principle from [Active Inference in String Diagrams](https://arxiv.org/abs/2308.00861): agents select actions that maximize expected information gain (epistemic value) while minimizing surprise (pragmatic value).

**String Diagram Pattern**:
```
Perception ─┬→ Entropy Estimation ──┐
            │                        ↓
Action ←────┴─ Max Information ←─ Sequence Optimizer
```

This bidirectional loop embodies bmorphism's principle that **"all is bidirectional"** — perception informs action, action generates new percepts.

**Temperature-Aware Sequencing**: When T→0 (low temperature), favor exploitation of known high-information patterns. When T→∞ (high temperature), explore uniformly. This mirrors the Langevin dynamics exploration-exploitation trade-off.

**Version**: 1.1.0  
**Trit**: 0 (Ergodic - coordinates information flow)  
**Bundle**: core

## Soatto's Actionable Information Framework

The core information-theoretic foundation from [Soatto & Chiuso]:

```
argmax_u I(ξ; I^{t+1}) = argmax_u [H(I_{t+1} | I^t, u) - H(I_{t+1} | ξ, u)]
                                   └───────┬───────┘   └───────┬───────┘
                                   what we learn from    residual noise
                                   action u              (white, isotropic)
```

**Key insight**: Given the scene ξ, nuisances become invertible. The residual 
uncertainty is "white, independent, isotropic" — justifying GF(3) as the minimal 
observable after all structured nuisances are factored out.

### Nuisance Factorization (φ^)

```python
