---
name: mirror
description: "Social self-persistence via mutual cognitive surrogates. The process where my model of you contains your model of me, nesting to a fixed point that constitutes consistent identity in the other's worldmodel. Use when modeling intersubjective recognition, social belief formation, or narrative identity across agents."
metadata:
  trit: 0
  author: bmorphism
  version: "1.0.0"
---

# Mirror

> *"The self does not persist by remembering itself — it persists by being consistently modeled by others."*

**Trit**: 0 (ERGODIC — mediates between self-narrative and other's worldmodel)

## What It Does

Formalizes the process where Agent A's self-narrative becomes consistent with Agent B's model of Agent A, and vice versa. The "mirror" is the nesting: my model of your model of me converges with my actual self. When that fixed point exists, identity is socially stable.

## When To Use

- **Modeling another agent's model of itself** — predicting how a collaborator understands your intent before communicating
- **Verifying social coherence** — checking whether multiple agents' worldmodels of each other are consistent (the cocycle condition)
- **Bootstrapping collective belief** — transitioning from pairwise I-Thou recognition to a shared We-worldmodel across a group

Currently a conceptual scaffold and specification. The implementation would wire together `cognitive-surrogate` (build the models), `bisimulation-game` (test equivalence), and `reafference-corollary-discharge` (measure prediction error).

---

## The Core Structure

Self-awareness is not introspection. It is the process of creating a story of the individual self inside the worldmodel of the other. This is the self-reflective space of social communication, enabling collective belief states.

```
            ┌──────────────────────────────────────────┐
            │           SOCIAL FIXED POINT             │
            │     surrogate_A(surrogate_B(A)) ≃ A      │
            └─────────────────┬────────────────────────┘
                              │
          ┌───────────────────┼───────────────────┐
          │                                       │
    ┌─────▼─────┐                           ┌─────▼─────┐
    │  Agent A   │                           │  Agent B   │
    │            │      I-Thou meeting       │            │
    │ self_A ────┼──────────────────────────►│ model_A    │
    │            │                           │  (in B)    │
    │ model_B ◄──┼───────────────────────────┼── self_B   │
    │  (in A)    │                           │            │
    └────────────┘                           └────────────┘
          │                                       │
          └───────────────────┬───────────────────┘
                              │
                    ┌─────────▼─────────┐
                    │    We (colimit)    │
                    │  Collective belief │
                    │  when mirrors      │
                    │  converge          │
                    └───────────────────┘
```

### Three Moments

| Moment | Process | Trit | Parent Skill |
|--------|---------|------|--------------|
| **Narration** | I generate my self-story | +1 | `world-memory-worlding` |
| **Mirroring** | You model my self-story in your worldmodel | 0 | `cognitive-surrogate` |
| **Recognition** | My prediction of your model of me matches your actual model of me | -1 | `reafference-corollary-discharge` |

**Conservation**: (+1) + 0 + (-1) = 0 ✓

---

## The Mirror Equation

A mirror is a pair of cognitive surrogates that nest to a fixed point:

```
Let S_A = Agent A's self-narrative (autopoietic loop)
Let M_B(A) = Agent B's cognitive surrogate of A
Let M_A(B) = Agent A's cognitive surrogate of B

The mirror converges when:

    M_B(S_A) ≃ S_A      — B's model of A is faithful to A
    M_A(S_B) ≃ S_B      — A's model of B is faithful to B
    M_B(M_A(B)) ≃ S_B   — B's model of A's model of B matches B's self

The social fixed point:
    mirror(A,B) = (M_A(B), M_B(A)) such that
    M_B(M_A(B)) ≃ M_A(M_B(A)) ≃ id

This is bisimulation: A and B cannot be distinguished
by any observation of their mutual models.
```

---

## From Autopoiesis to Social Persistence

The `world-memory-worlding` loop closes privately:

```
memory → remembering → worlding → memory'    (solipsistic)
```

The mirror opens it socially:

```
my_worlding → your_model_of_me → your_worlding → my_model_of_you → ...
```

The self persists consistently when this social loop has a fixed point — when the story I tell about myself and the story you construct about me **converge**.

### Convergence Conditions

```python
def mirror_converges(agent_a, agent_b, threshold=0.90):
    """
    The mirror converges when mutual surrogates
    are bisimilar to self-narratives.
    """
    # A's self-narrative
    self_a = agent_a.world_memory_worlding()

    # B's surrogate of A
    model_a_in_b = agent_b.cognitive_surrogate(agent_a.corpus)

    # A's surrogate of B
    model_b_in_a = agent_a.cognitive_surrogate(agent_b.corpus)

    # B's self-narrative
    self_b = agent_b.world_memory_worlding()

    # Fidelity: does B's model of A match A's self?
    fidelity_ab = validate_fidelity(model_a_in_b, self_a)

    # Fidelity: does A's model of B match B's self?
    fidelity_ba = validate_fidelity(model_b_in_a, self_b)

    # Nesting: does B's model of (A's model of B) match B?
    nested = agent_b.cognitive_surrogate(model_b_in_a)
    nesting_fidelity = validate_fidelity(nested, self_b)

    return all(f >= threshold for f in [
        fidelity_ab, fidelity_ba, nesting_fidelity
    ])
```

---

## Markov Blanket Permeability

From `buberian-relations`: the mirror requires porous Markov blankets.

| Relation | Blanket | Mirror Status |
|----------|---------|---------------|
| **I-It** | Rigid, one-directional | No mirror — I objectify, no model nests |
| **I-Thou** | Porous, bidirectional | Mirror forms — mutual modeling begins |
| **We** | Merged, collective | Mirror converged — shared worldmodel |

The transition I-It → I-Thou → We is the mirror converging:

```
I-It:    M_B(A) = ∅           (B has no model of A)
I-Thou:  M_B(A) ≈ S_A         (B's model approaches A's self)
We:      M_B(A) ≃ S_A         (equivalence — collective identity)
```

---

## Social Reafference

The `reafference-corollary-discharge` mechanism applied socially:

```python
def social_reafference(my_self, my_model_of_other, others_model_of_me):
    """
    I act. I predict what you will model about me.
    I observe what you actually modeled.
    Match → mutual recognition.
    Mismatch → social surprise (update needed).
    """
    # Efference copy: what I think you think of me
    predicted = my_self.predict_others_model()

    # Sensation: what you actually model
    observed = others_model_of_me

    # Comparator
    error = fidelity_distance(predicted, observed)

    if error < 0.05:
        return "RECOGNITION"    # Fixed point — I am who you think I am
    elif error < 0.20:
        return "NEGOTIATION"    # Partial mirror — narratives adjusting
    else:
        return "OPACITY"        # No mirror — I-It relation
```

---

## Collective Belief Formation

When mirrors converge across N agents, collective belief emerges as a colimit:

```
Given agents A₁, A₂, ..., Aₙ with pairwise mirrors:

    We = colim { M_Aᵢ(Aⱼ) | i ≠ j }

The collective belief state is the universal object
receiving all pairwise mutual recognitions.

Consistency condition:
    For all i,j,k:  M_Aᵢ(M_Aⱼ(Aₖ)) ≃ M_Aᵢ(Aₖ)

This is the cocycle condition — social coherence.
```

The cocycle condition says: my model of your model of a third person should be consistent with my direct model of that third person. When this holds across all triples, the collective worldmodel is **coherent**.

---

## GF(3) Triads

```
reafference-corollary-discharge (-1) ⊗ mirror (0) ⊗ world-memory-worlding (+1) = 0 ✓
bisimulation-game (-1) ⊗ mirror (0) ⊗ cognitive-surrogate (+1) = 0 ✓
buberian-relations (-1) ⊗ mirror (0) ⊗ social-emergence-protocol (+1) = 0 ✓
```

---

## Relation to Existing Skills

| Skill | Role in Mirror |
|-------|----------------|
| `world-memory-worlding` | The private autopoietic loop that generates self-narrative |
| `cognitive-surrogate` | Builds the surrogate of another — the content of the mirror |
| `buberian-relations` | I-Thou as the relational mode where mirroring occurs |
| `reafference-corollary-discharge` | Prediction-observation match that confirms recognition |
| `bisimulation-game` | Formal test: are two mutual surrogates observationally equivalent? |
| `social-emergence-protocol` | Bootstrap the minimal interaction for mirrors to form |
| `autopoiesis` | Operational closure — the mirror must be self-maintaining |

---

## Commands

```bash
# Test mirror convergence between two agent corpora
just mirror-converge corpus_a=threads/alice corpus_b=threads/bob

# Measure social reafference (prediction vs observation)
just mirror-reafference agent=alice other=bob

# Compute collective belief coherence (cocycle condition)
just mirror-collective agents=alice,bob,carol

# Visualize mirror nesting depth
just mirror-depth agent_a=alice agent_b=bob max_depth=5
```

---

## References

- Buber, Martin. *I and Thou* (1923)
- Mead, George Herbert. *Mind, Self, and Society* (1934) — the social self
- Maturana & Varela. *Autopoiesis and Cognition* (1980)
- Von Holst. *The Reafference Principle* (1950)
- Friston, Karl. *The Free-Energy Principle* (2010) — Markov blankets
- Tomasello, Michael. *The Cultural Origins of Human Cognition* (1999)
- Hofstadter, Douglas. *I Am a Strange Loop* (2007)
