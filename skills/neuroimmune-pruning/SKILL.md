---
name: neuroimmune-pruning
description: "Immune substrate of biological active inference — microglia + complement (C1q→C3b→CR3) tag and phagocytose synapses, acting as the body's TMS justifier / garbage collector. Immunosurveillance = nogood-repair; autoimmunity = the false nogood. Use when modeling immune editing of neural priors, neuroinflammation gating plasticity, or the immune-vascular latch coupling."
license: MIT
metadata:
  trit: 0
  source: "https://doi.org/10.1126/science.1202529"
---

# neuroimmune-pruning

The **immune substrate** (0 / witness) of the three-substrate vasocomputation stack. The neuroimmune system is the body's **garbage collector and TMS justifier**: microglia, using the **classical complement cascade (C1q → C3b opsonization → CR3-mediated phagocytosis)**, tag and eliminate synapses — literally editing the neural prior set. Perivascular mast cells couple the immune leg to the vascular leg; pro-inflammatory cytokines (IL-1β, TNF-α) gate whether a held pattern is allowed to consolidate.

## Use When

- Modeling the immune system as the *editor* of neural priors (microglial synaptic pruning)
- Neuroinflammation as precision-weighting on the consolidation (−1) step
- The immune–vascular coupling that maintains or releases a latch (`latched-hyperprior`)
- Distinguishing healthy immunosurveillance (nogood-repair) from autoimmunity (false nogood)

## Core Concepts

- **Complement tagging = `EnsureJustification`**: a synapse with no closing justification is opsonized by C1q/C3b and phagocytosed by microglia — a *measured* retraction (a nogood), not an assigned one. (Stevens 2007; Schafer 2012.)
- **Immunosurveillance = the −1 / coplay nogood-repair leg**: the body detects defected/latched/cancerous subagents and clears them. Levin: latched cells that bioelectrically disconnect are exactly what surveillance should catch.
- **Autoimmunity = the false nogood**: complement tags *self* — excess C3/C4 synaptic pruning is implicated in schizophrenia and Alzheimer's. This is the worm **Goodharting its self/non-self boundary**: forcing *content-H¹* (real signal) to 0 by attacking valid synapses.
- **Latch maintenance**: latch → hypoxia (HIF-1α) → inflammatory recruitment → more VSMC tone. Trying to wall off a perturbation, the immune system can *stabilize* the latch — the latch spiral as a granuloma-like, immune-defended locus.
- **Mast cells**: perivascular sentinels; degranulation (a fast "grab") triggers the vascular event that becomes a latch.

## GF(3) Balanced Triad

```
vasocomputation (+1) ⊗ neuroimmune-pruning (0) ⊗ neural-potentiation (−1) = 0 (mod 3)
```

**Skill Trit**: 0 (Witness — the justifier/GC that decides what is kept; cf. the PAM `JustifierAgent` maintaining the justification lattice).

## Honesty markers

Grounded: microglial complement-mediated synaptic pruning; perivascular mast cells; cytokine modulation of LTP; HIF/hypoxia–inflammation; immunosurveillance of cancer. **Speculative weld (marked, not asserted)**: framing the immune system as a free-energy / active-inference learner, and the GF(3) substrate→trit assignment as an organizing correspondence.

## Concomitant Skills

| Skill | Trit | Interface |
|-------|------|-----------|
| `vasocomputation` | +1 | vascular substrate it co-regulates |
| `neural-potentiation` | −1 | gates / prunes the synaptic store |
| `latched-hyperprior` | −1 | unlatch (resolve) vs. defend (granuloma) |
| `cybernetic-immune` | 0 | immune system as a cybernetic controller |
| `sheaf-cohomology` | 0 | pruning = trivializing a nogood cocycle |
| `affective-taxis` | −1 | self/non-self boundary = valence boundary |

## References

- Stevens, B. et al. (2007). *The classical complement cascade mediates CNS synapse elimination*. Cell 131(6).
- Schafer, D.P. et al. (2012). *Microglia sculpt postnatal neural circuits in an activity- and complement-dependent manner*. Neuron 74(4). doi:10.1126/science.1202529 (program).
- Yirmiya, R. & Goshen, I. (2011). *Immune modulation of learning, memory, neural plasticity and neurogenesis*. Brain Behav. Immun. 25(2).
- Levin, M. (2022). *TAME*. Front. Syst. Neurosci. 16. (Defection / cancer / surveillance.)
