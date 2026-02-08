---
name: alife
description: Comprehensive Artificial Life skill combining ALIFE2025 proceedings,
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ALIFE: Artificial Life Comprehensive Skill

**Status**: ✅ Production Ready
**Trit**: +1 (PLUS - generative/creative)
**Sources**: ALIFE2025 Proceedings + Classic Texts + Code Repos

## Quick Reference

| Resource | Content |
|----------|---------|
| **ALIFE2025** | 337 pages, 80+ papers, 153 figures, 100+ equations |
| **Axelrod** | Evolution of Cooperation, TIT-FOR-TAT, Prisoner's Dilemma |
| **Epstein-Axtell** | Sugarscape, Growing Artificial Societies |
| **ALIEN** | CUDA 2D particle engine (ALIFE 2024 winner) |
| **Lenia** | Continuous cellular automata |
| **Concordia** | DeepMind generative agent-based models |

## Core Concepts

### 1. Evolutionary Dynamics

```latex
% Fitness-proportionate selection
P(i) = \frac{f_i}{\sum_{j=1}^{N} f_j}

% Replicator dynamics
\dot{x}_i = x_i \left[ f_i(x) - \bar{f}(x) \right]
```

### 2. Prisoner's Dilemma & Cooperation

```
         Cooperate    Defect
Cooperate   R,R        S,T
Defect      T,S        P,P

where T > R > P > S (temptation > reward > punishment > sucker)
```

**TIT-FOR-TAT Strategy** (Axelrod):
1. Cooperate on first move
2. Then do whatever opponent did last round

Properties: **Nice** (never defects first), **Retaliatory**, **Forgiving**, **Clear**

### 3. Cellular Automata

**Elementary CA** (Wolfram):
```
Rule 110: [111→0] [110→1] [101→1] [100→0] [011→1] [010→1] [001→1] [000→0]
```

**Lenia** (Continuous CA):
```latex
A^{t+\Delta t} = \left[ A^t + \Delta t \cdot G(K * A^t) \right]_0^1

G_{\mu,\sigma}(x) = 2e^{-\frac{(x-\mu)^2}{2\sigma^2}} - 1
```

**Flow-Lenia** (Mass-conserving, arXiv:2506.08569):
```latex
% Velocity field from kernel convolution
\vec{v}(x) = \nabla G(K * A^t)

% Mass-conserving update via continuity equation
A^{t+1} = A^t - \nabla \cdot (A^t \cdot \vec{v})

% With multispecies extension
A_i^{t+1} = A_i^t - \nabla \cdot \left(A_i^t \cdot \sum_j w_{ij} \vec{v}_j\right)
```

**H-Lenia** (Hierarchical):
```latex
\left[\left[A_i^t + \Delta t G(K * A_i^t)\right]_0^1 + \sum_{j \in N(i)} k_{ji