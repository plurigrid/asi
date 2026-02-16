# Omniglot Challenge Skill

The Lake-Salakhutdinov-Tenenbaum challenge for human-level concept learning through probabilistic program induction. Learn new concepts from a single example.

## The Challenge

Five tasks that a single model must perform at human level:

| Task | Description | BPL Performance |
|------|-------------|-----------------|
| **One-shot classification** | Identify character from 20 alternatives | 3.3% error (human: 4.5%) |
| **Parsing** | Infer stroke decomposition | 59% ID level |
| **Exemplar generation** | Generate new examples of a character | 52% ID level |
| **Concept generation (constrained)** | Create new characters for an alphabet | 49% ID level |
| **Concept generation (unconstrained)** | Create novel characters from scratch | 51% ID level |

**ID level** = Visual Turing Test identification rate (50% = indistinguishable from human)

## Core Insight

> "People learning new concepts can often generalize successfully from just a single example... We present a computational model that represents concepts as simple programs that best explain observed examples under a Bayesian criterion."
> — Lake, Salakhutdinov, Tenenbaum (Science, 2015)

## Bayesian Program Learning (BPL)

Three key ingredients:

1. **Compositionality**: Concepts built from simpler primitives (strokes, parts)
2. **Causality**: Captures how data was actually generated (motor programs)
3. **Learning to learn**: Prior experience accelerates new concept acquisition

```
Character = Program(strokes, relations, noise)
P(concept | example) ∝ P(example | concept) × P(concept)
```

## Dataset

- **50 alphabets** from world's writing systems
- **1,623 characters** total
- **20 examples** per character (different writers)
- **Stroke data** included (not just images)

### Splits

| Split | Alphabets | Classes | Purpose |
|-------|-----------|---------|---------|
| Original | 30 background | 964 | Standard learning-to-learn |
| Minimal | 5 background | 146 | Human-like prior experience |
| Augmented | 40 (4× rotation) | 4800 | Extended meta-learning |

## Why Current ML Falls Short

From the 3-year progress report (2019):

| Model | Within-alphabet | Minimal split |
|-------|-----------------|---------------|
| BPL | **3.3%** | **4.2%** |
| Humans | 4.5% | — |
| Prototypical Net | 13.7% | 30.1% |
| RCN | 7.3% | — |
| Siamese Net | 8.0% | — |

> "Recent approaches are still far from human-like concept learning on Omniglot, a challenge that requires performing many tasks with a single model."

## The Real Challenge

**NOT just one-shot classification.** The challenge is:

1. Single model for ALL five tasks
2. Minimal background training (5 alphabets, like humans)
3. Using stroke/motor program data, not just images
4. Compositionality and causality, not "learning from scratch"

## References

- Lake, Salakhutdinov, Tenenbaum (2015). "Human-level concept learning through probabilistic program induction." *Science* 350:1332-1338. [PDF](https://www.cs.cmu.edu/~rsalakhu/papers/LakeEtAl2015Science.pdf)

- Lake, Salakhutdinov, Tenenbaum (2019). "The Omniglot challenge: a 3-year progress report." *Current Opinion in Behavioral Sciences* 29:97-104. [PDF](https://www.cs.princeton.edu/~bl8144/papers/LakeEtAlOmniglotProgress.pdf)

- Dataset: [github.com/brendenlake/omniglot](https://github.com/brendenlake/omniglot)

## Trit Assignment

- **Trit**: 0 (ERGODIC - coordinator)
- **GF(3) Role**: Bridges generative and discriminative approaches

## Local Implementation

```python
# ~/ies/worlding_skill_omniglot_entropy.py
from worlding_skill_omniglot_entropy import (
    ParallelOmniglotLearner,
    OmniglotCharacterFamily,
    BidirectionalCharacterLearner  # Read ↔ Write coupling
)
```

## Connection to Active Inference

From Parr-Friston (Active Inference):
> "Tenenbaum et al. (2006) established structure learning as a key objective in computational modeling and cognitive science."

BPL shares with Active Inference:
- **Generative models** of sensory data
- **Hierarchical priors** learned from experience  
- **Inference** as explanation of observations

## Key Quote

> "Hofstadter famously argued that learning to recognize the characters in all the ways that people do contains most of the fundamental challenges of AI."

## Gay.jl Colors (seed 2015)

| Task | Color |
|------|-------|
| Classification | `#9858E7` |
| Parsing | `#A81AA7` |
| Exemplar Gen | `#BCD86F` |
| Concept Gen (C) | `#F283CD` |
| Concept Gen (U) | `#188DB2` |


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
