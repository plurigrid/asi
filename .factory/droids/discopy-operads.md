---
name: discopy-operads
description: DiscoPy Operads Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# DiscoPy Operads Skill

> **Repo Color:** `#64e3ec` | **Seed:** `0x128b6ef4564e3a00` | **Index:** 224/1055

DisCoPy: Python toolkit for computing with string diagrams, monoidal categories, and operads.

## bmorphism Contributions

> *"universal topos construction for social cognition and democratization of mathematical approach to problem-solving to all"*
> — [Plurigrid: the story thus far](https://gist.github.com/bmorphism/a400e174b9f93db299558a6986be0310)

**Operads as Skill Composition**: DisCoPy's operad module implements the colored operad structure that bmorphism uses for skill composition. Each skill is an operation with typed inputs/outputs; composition follows operad laws.

**Active Inference Connection**: The operadic structure enables hierarchical [Active Inference in String Diagrams](https://arxiv.org/abs/2308.00861) — nested perception-action loops where higher-level beliefs parameterize lower-level policies.

**GF(3) Colored Operads**: Following the paper "On the homotopy theory of equivariant colored operads" (Bonventre & Pereira), colors can encode trit values {-1, 0, +1} for balanced skill composition.

## Quick Reference

```python
from discopy.monoidal import Ty, Box, Id, Diagram
from discopy.grammar.cfg import Tree, Rule, Word, Operad, Algebra
from discopy import symmetric, braided, compact, frobenius, hypergraph
```

## String Diagram Syntax

```python
# Types are objects in monoidal categories
x, y, z = Ty('x'), Ty('y'), Ty('z')
unit = Ty()  # monoidal unit

# Tensor product (horizontal composition)
xy = x @ y  # x ⊗ y

# Boxes are morphisms
f = Box('f', x, y)           # f: x → y
g = Box('g', y, z)           # g: y → z

# Sequential composition (vertical)
fg = f >> g                   # g ∘ f: x → z

# Parallel composition (tensor of morphisms)
f_par_g = f @ g              # f ⊗ g: x ⊗ y → y ⊗ z

# Identity morphisms
idx = Id(x)                  # id_x: x → x

# Interchange law
d = Id(x) @ g >> f @ Id(z)   # = (f @ g).interchange(0, 1)
```

#