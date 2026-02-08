---
name: open-games
description: Open Games Skill (ERGODIC 0)
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Open Games Skill (ERGODIC 0)

> Compositional game theory via Para/Optic structure

**Trit**: 0 (ERGODIC)
**Color**: #26D826 (Green)
**Role**: Coordinator/Transporter

## bmorphism Contributions

> *"Parametrised optics model cybernetic systems, namely dynamical systems steered by one or more agents. Then ⊛ represents agency being exerted on systems"*
> — [@bmorphism](https://github.com/bmorphism), GitHub bio

> *"We introduce open games as a compositional foundation of economic game theory. A compositional approach potentially allows methods of game theory and theoretical computer science to be applied to large-scale economic models"*
> — [Compositional Game Theory](https://arxiv.org/abs/1603.04641), Ghani, Hedges, Winschel, Zahn (2016)

**Key Papers** (from bmorphism's Plurigrid references):
- [Compositional game theory](https://arxiv.org/abs/1603.04641) - open games as symmetric monoidal category morphisms
- [Morphisms of Open Games](https://www.sciencedirect.com/science/article/pii/S1571066118300884) - connection between lenses and compositional game theory
- [Bayesian Open Games](https://compositionality.episciences.org/13528/pdf) - stochastic environments, incomplete information
- [Categorical Cybernetics Manifesto](https://julesh.com/posts/2019-11-27-categorical-cybernetics-manifesto.html) - control theory of complex systems

**CyberCat Institute Connection**: Open games are central to the [CyberCat Institute](https://cybercat.institute) research program on categorical cybernetics.

Related to bmorphism's work on:
- [plurigrid/act](https://github.com/plurigrid/act) - active inference + ACT + enacted cognition
- Play/Coplay bidirectional feedback structure

## Core Concept

Open games are morphisms in a symmetric monoidal category:

```
        ┌───────────┐
   X ──→│           │──→ Y
        │  Game G   │
   R ←──│           │←── S
        └───────────┘
```

Where:
- **X → Y**: Forward play (strategies)
- **S → R**: Backward coplay (utilities)

## The Para/