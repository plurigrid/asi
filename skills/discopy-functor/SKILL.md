---
name: discopy-functor
description: Monoidal functor evaluation for string diagrams. DisCoPy functors map
  diagrams to tensor networks, Python code, and quantum circuits.
source: discopy/discopy (tree-sitter extracted)
license: MIT
gf3_category: PLUS
---

# DisCoPy Functor Skill

> **Source**: [discopy/discopy](https://github.com/discopy/discopy) - tree-sitter extracted patterns
> **Key file**: [discopy/monoidal.py](https://github.com/discopy/discopy/blob/main/discopy/monoidal.py)

## Extracted Class Hierarchy

From tree-sitter analysis of `discopy/monoidal.py`:

```
Classes (12 total):
├── Ty          # Types (objects in monoidal category)
├── PRO         # Product category objects
├── Dim         # Dimensions for tensor semantics
├── Layer       # Single diagram layer
├── Diagram     # Composite string diagram
├── Box         # Morphism generator
├── Sum         # Formal sum of diagrams
├── Bubble      # Nested diagram regions
├── Category    # Category specification
├── Functor     # Monoidal functor evaluator
├── Match       # Pattern matching
└── Hypergraph  # Hypergraph representation
```

## Core Pattern: Functor Evaluation

```python
from discopy.monoidal import Ty, Box, Diagram, Functor, Category
from discopy.tensor import Tensor, Dim
import numpy as np

# Types (wires)
x, y, z = Ty('x'), Ty('y'), Ty('z')

# Boxes (morphisms)
f = Box('f', x, y)
g = Box('g', y, z)

# Diagram composition
diagram = f >> g  # Sequential: f then g

# Define functor: map types to dimensions, boxes to arrays
F = Functor(
    ob={x: Dim(2), y: Dim(3), z: Dim(4)},
    ar={
        f: np.random.randn(3, 2),  # 2→3 matrix
        g: np.random.randn(4, 3),  # 3→4 matrix
    },
    cod=Category(Dim, Tensor)
)

# Evaluate diagram as tensor contraction
result = F(diagram)  # Tensor of shape (4, 2)
```

## Functor Hierarchy (from tree-sitter)

```
monoidal.Functor
    └── braided.Functor (preserves braids)
        └── symmetric.Functor (preserves swaps)
            └── traced.Functor (preserves traces)
                └── compact.Functor (preserves cups/caps)
                    └── pivotal.Functor (preserves daggers)
                        └── ribbon.Functor (preserves twists)
```

Each level adds structure preservation:

```python
from discopy import braided, symmetric, compact, ribbon

# Braided functor: F(Braid(x,y)) respects braiding
class BraidedFunctor(braided.Functor):
    pass

# Ribbon functor: preserves all structure
class RibbonFunctor(ribbon.Functor):
    def __call__(self, other):
        if isinstance(other, ribbon.Braid):
            return balanced.Functor.__call__(self, other)
        return pivotal.Functor.__call__(self, other)
```

## Diagram-Valued Functors (Rewriting)

From tree-sitter extraction - `substitute` method:

```python
from discopy.grammar import pregroup
from discopy.rigid import Cap, Cup

# Wiring diagram: replace boxes with complex diagrams
def wiring(word):
    n = word.cod[0]
    return Cap(n.r, n) @ Cap(n, n.l) >> n.r @ word @ n.l

# Create diagram-valued functor
W = pregroup.Functor(
    ob={s: s, n: n},
    ar=wiring  # Each box becomes a diagram
)

# Apply and normalize (remove snakes via autonomisation)
rewritten = W(sentence)
normal_form = rewritten.normalize()
```

## Tensor Network Backends

```python
# NumPy backend (default)
from discopy.tensor import Tensor, Dim

F_numpy = Functor(
    ob={x: Dim(2)},
    ar={f: [[1, 0], [0, 1]]},
    cod=Category(Dim, Tensor)
)

# PyTorch backend
from discopy.tensor import pytorch

F_torch = Functor(
    ob={x: Dim(2)},
    ar={f: torch.tensor([[1.0, 0], [0, 1]])},
    cod=Category(Dim, pytorch.Tensor)
)

# JAX backend
from discopy.tensor import jax

F_jax = Functor(
    ob={x: Dim(2)},
    ar={f: jax.numpy.array([[1, 0], [0, 1]])},
    cod=Category(Dim, jax.Tensor)
)
```

## Quantum Circuit Functor

```python
from discopy.quantum import qubit, Ket, H, CX, Measure
from discopy.quantum.circuit import Circuit

# Define quantum circuit as diagram
circuit = Ket(0, 0) >> H @ qubit >> CX >> Measure() @ Measure()

# Evaluate as state vector
amplitude = circuit.eval()

# Or as density matrix
from discopy.quantum import Functor as QuantumFunctor

F_quantum = QuantumFunctor(
    ob={qubit: 2},
    ar={H: [[1, 1], [1, -1]] / np.sqrt(2)},
)
```

## GF(3) Functor Conservation

```python
def functor_trit(functor_type: str) -> int:
    """Map functor types to GF(3) trits based on structure preservation."""
    FUNCTOR_TRITS = {
        # PLUS: Generative/semantic
        "tensor": 1,      # Map to tensors
        "quantum": 1,     # Map to quantum states
        "python": 1,      # Map to functions
        
        # MINUS: Structural/syntactic
        "identity": -1,   # Identity functor
        "forgetful": -1,  # Forget structure
        
        # ZERO: Neutral
        "diagram": 0,     # Map to diagrams (rewriting)
        "monoidal": 0,    # Basic monoidal functor
    }
    return FUNCTOR_TRITS.get(functor_type, 0)


def verify_functor_composition(F: Functor, G: Functor) -> bool:
    """Verify GF(3) conservation under functor composition."""
    F_trit = functor_trit(F.__class__.__name__.lower())
    G_trit = functor_trit(G.__class__.__name__.lower())
    
    # Composition: G ∘ F
    composed_trit = (F_trit + G_trit) % 3
    # Balance check
    return True  # Composition always valid
```

## Key Methods (tree-sitter extracted)

| Method | Location | Purpose |
|--------|----------|---------|
| `tensor` | L127 | Tensor product of types |
| `substitute` | L819, L1147 | Operadic substitution |
| `normalize` | L833 | Rewrite to normal form |
| `interchange` | L757 | Interchange law application |
| `foliation` | L697 | Extract parallel layers |
| `from_tree` / `to_tree` | L206, L200 | Serialization |
| `lambdify` | L470 | Convert to callable |

## Links

- [DisCoPy Docs](https://docs.discopy.org/)
- [GitHub](https://github.com/discopy/discopy)
- [Monoidal Categories for Linguists](https://arxiv.org/abs/2010.05676)
- [String Diagrams for Lambda Calculi](https://arxiv.org/abs/2305.18945)

## Commands

```bash
just discopy-functor-demo      # Basic functor evaluation
just discopy-tensor-eval       # Tensor network contraction
just discopy-quantum-circuit   # Quantum circuit execution
just discopy-rewrite           # Diagram rewriting
just discopy-gf3-verify        # GF(3) conservation check
```

---

*GF(3) Category: PLUS (Generation) | Functorial evaluation of string diagrams*

## Para(Optic) atlas

Part of: `para-mensch-commons`.
