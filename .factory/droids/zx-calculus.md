---
name: zx-calculus
description: Coecke's ZX-calculus for quantum circuit reasoning via string diagrams with Z-spiders (green) and X-spiders (red)
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ZX-Calculus

**Trit**: -1 (MINUS - foundational/classical notation)
**Origin**: Coecke & Duncan (2008)
**Principle**: Quantum computation via string diagram rewriting

---

## Overview

ZX-calculus is a graphical language for quantum computing where:
- **Z-spiders** (green): Phase gates in computational basis
- **X-spiders** (red): Phase gates in Hadamard basis
- **Wires**: Qubits
- **Rewrite rules**: Simplify circuits

## Basic Elements

```
Z-spider (green):        X-spider (red):         Hadamard:
    │                        │                      ╲ ╱
  ┌─┴─┐                    ┌─┴─┐                     ─
  │ α │  = e^{iα}|0⟩⟨0|    │ α │  = H·Z(α)·H        ─
  └─┬─┘    + |1⟩⟨1|        └─┬─┘                    ╱ ╲
    │                        │
```

## GF(3) Color Assignment

| Spider | Color | Trit | Basis |
|--------|-------|------|-------|
| Z | Green #26D826 | 0 | Computational |
| X | Red #D82626 | +1 | Hadamard |
| H-edge | Blue #2626D8 | -1 | Transition |

**Conservation**: Green(0) + Red(+1) + Blue(-1) = 0 ✓

## Core Rules

### Spider Fusion
```
  │       │           │
┌─┴─┐   ┌─┴─┐       ┌─┴─┐
│ α │───│ β │  =    │α+β│
└─┬─┘   └─┬─┘       └─┬─┘
  │       │           │
```

### Bialgebra (Hopf)
```
  ╲ ╱       │ │
   X    =   │ │
  ╱ ╲       │ │
```

### Color Change
```
┌───┐     ┌───┐
│ Z │──H──│ X │
└───┘     └───┘
```

## DisCoPy Implementation

```python
from discopy.quantum.zx import Z, X, H, Id, SWAP, Cap, Cup

# Bell state preparation
bell = Cap(Z(0), Z(0)) >> (Id(1) @ H) >> CNOT

# ZX diagram
diagram = Z(1, 2, phase=0.5) >> (X(1, 1, phase=0.25) @ Z(1, 1))

# Simplify via rewrite rules
simplified = diagram.normal_form()

# Extract circuit
circuit = simplified.to_circuit()
```

## Musical Notation (Quantum Guitar)

From Abdyssagin & Coecke's "Bell" composition:

```
Staff 1 (Piano):     Staff 2 (Quantum Guitar):
    ┌─Z─┐                 ┌─X─┐
    │   │                 │   │
────┴───┴────        ─────┴───┴─────
    Bell pair            Measuremen