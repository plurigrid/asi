---
name: discopy
description: "DisCoPy: Python library for computing with string diagrams - monoidal"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# DisCoPy: String Diagrams in Python

> *"String diagrams are the syntax, functors are the semantics."*

## bmorphism Contributions

> *"all is bidirectional"*
> — [@bmorphism](https://gist.github.com/bmorphism/ead83aec97dab7f581d49ddcb34a46d4), Play/Coplay gist

**Active Inference Implementation**: DisCoPy provides the foundation for implementing [Active Inference in String Diagrams](https://arxiv.org/abs/2308.00861) (Tull, Kleiner, Smithe). The paper's core insight — that perception and action form a bidirectional loop — maps directly to DisCoPy's composition operators:
- **Sequential** (`>>`) → temporal flow (action → perception → action)
- **Parallel** (`@`) → concurrent sensory channels
- **Dagger** (`[::-1]`) → time reversal (perception as action's adjoint)

**Categorical Cybernetics**: DisCoPy's parametrised optics implement the cybernetic lens pattern from [Towards Foundations of Categorical Cybernetics](https://arxiv.org/abs/2105.06332), enabling the Play/Coplay duality bmorphism references.

**String Diagram Coloring**: Gay.jl colors can be applied to DisCoPy diagrams for deterministic visualization — each wire type gets a consistent color from the splittable RNG.

## Overview

DisCoPy is a Python library for computing with **string diagrams** - the graphical language of monoidal categories. It provides:

1. **Categorical Framework**: Ty, Ob, Box, Arrow, Diagram, Category
2. **Operads**: CFG as free operads, operad algebras, colored operads
3. **Quantum Computing**: Circuits, gates, ZX-calculus, pytket/qiskit integration
4. **QNLP**: Pregroup grammars, DisCoCat, ansätze for quantum NLP
5. **Tensor Networks**: NumPy/JAX/PyTorch backends, tensornetwork contraction
6. **Visualization**: Matplotlib/TikZ drawing with color customization

---

## Core Architecture (DeepWiki 2025-12-22)

### Class Hierarchy

```
Category
├── ob: Ob (objects/systems)
└── ar: Arrow (morphisms/processes)

Ob → Ty (monoidal: tuple of objects, tensor = concatenation)

Arrow → Diagram 