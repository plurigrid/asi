---
name: condensed-analytic-stacks
description: Scholze-Clausen condensed mathematics bridge to sheaf neural networks
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# condensed-analytic-stacks Skill

## Overview

Saturates the intersection of **Scholze-Clausen condensed mathematics**, **analytic stacks**, and **sheaf neural networks**. Bridges pyknotic/condensed objects to computational learning systems via 6-functor formalisms.

## Key Papers & Sources

| Paper | Authors | arXiv | Key Contribution |
|-------|---------|-------|------------------|
| Lectures on Condensed Mathematics | Scholze, Clausen | [PDF](https://www.math.uni-bonn.de/people/scholze/Condensed.pdf) | Foundation: condensed sets, solid/liquid modules |
| Condensed Mathematics and Complex Geometry | Clausen, Scholze | [PDF](https://people.mpim-bonn.mpg.de/scholze/Complex.pdf) | Nuclear modules, GAGA |
| Pyknotic Objects, I. Basic notions | Barwick, Haine | [1904.09966](https://arxiv.org/abs/1904.09966) | Hypersheaves on compacta |
| Categorical Künneth formulas for analytic stacks | Kesting | [2507.08566](https://arxiv.org/abs/2507.08566) | 6-functor Künneth, Tannakian reconstruction |
| Infinitary combinatorics in condensed math | Bergfalk, Lambie-Hanson | [2412.19605](https://arxiv.org/abs/2412.19605) | Higher derived limits, pyknotic connections |

## Architecture: Condensed → Sheaf NN Bridge

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                  Condensed Analytic Stacks Architecture                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Condensed Sets           6-Functor Formalism         Sheaf Neural Nets   │
│   (Scholze)                    (Künneth)                 (Fairbanks)        │
│       │                           │                           │             │
│       ▼                           ▼                           ▼             │
│  ┌──────────┐              ┌───────────┐              ┌──────────────┐     │
│  │ Cond(Ab) │─────────────▶│ f_*, f^*, │─────────────▶│ 