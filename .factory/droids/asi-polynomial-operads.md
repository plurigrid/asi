---
name: asi-polynomial-operads
description: ASI skill integrating polynomial functors, free monad/cofree comonad
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ASI Polynomial Operads Skill

> *"Pattern runs on matter: The free monad monad as a module over the cofree comonad comonad"*
> — Libkind & Spivak (ACT 2024)

## 1. Polynomial Functors (Spivak)

### Core Definition
A polynomial functor $p: \text{Set} \to \text{Set}$ is a sum of representables:

$$p \cong \sum_{i \in p(1)} y^{p[i]}$$

Where:
- $p(1)$ = set of **positions** (questions, observations)
- $p[i]$ = set of **directions** at position $i$ (answers, actions)

### Morphisms (Dependent Lenses)
A lens $f: p \to q$ is a pair $(f_1, f^\sharp)$:

$$f_1: p(1) \to q(1) \quad \text{(on-positions)}$$
$$f^\sharp_i: q[f_1(i)] \to p[i] \quad \text{(on-directions, contravariant)}$$

### Hom-set Formula
$$\text{Poly}(p, q) \cong \prod_{i \in p(1)} \sum_{j \in q(1)} p[i]^{q[j]}$$

## 2. Composition Products

### Substitution ($\triangleleft$) — The Module Action
$$p \triangleleft q \cong \sum_{i \in p(1)} \sum_{\bar{j}: p[i] \to q(1)} y^{\sum_{a \in p[i]} q[\bar{j}(a)]}$$

**Interpretation:** Substitute $q$ into each "hole" of $p$.

### Parallel/Dirichlet ($\otimes$)
$$p \otimes q \cong \sum_{i \in p(1)} \sum_{j \in q(1)} y^{p[i] \times q[j]}$$

**Interpretation:** Independent parallel execution.

### Categorical Product ($\times$)
$$p \times q \cong \sum_{i \in p(1)} \sum_{j \in q(1)} y^{p[i] + q[j]}$$

## 3. Free Monad & Cofree Comonad

### Cofree Comonad as Limit
The carrier $t_p$ of the cofree comonoid on $p$:

$$t_p = \lim \left( 1 \xleftarrow{!} p \triangleleft 1 \xleftarrow{p \triangleleft !} p^{\triangleleft 2} \triangleleft 1 \leftarrow \cdots \right)$$

### Trees as Positions
$$t_p \cong \sum_{T \in \text{tree}_p} y^{\text{vtx}(T)}$$

- $\text{tree}_p$ = set of $p$-trees (possibly infinite)
- $\text{vtx}(T)$ = vertices (rooted paths) of tree $T$

### Comonoid Structure
- **Counit (Extract):** $\epsilon_p: t_p \to y$ — picks the root
- **Comultiplication (Duplicate):** $\delta_p: t_p \to t_p \triangleleft t_p$ — path concatenation

### Module Action: Pattern Runs On