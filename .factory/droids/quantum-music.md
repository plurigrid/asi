---
name: quantum-music
description: Quantum computer music composition and performance using quantum circuits, ZX-calculus notation, and quantum instruments
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Quantum Music

**Trit**: 0 (ERGODIC - bridging classical and quantum)
**Field**: Quantum Computer Music
**Reference**: Miranda (2022) "Quantum Computer Music" Springer

---

## Overview

Quantum Music encompasses:
1. **Composition**: Using quantum algorithms/circuits
2. **Notation**: ZX-calculus augmented scores
3. **Instruments**: Quantum Guitar, Q1Synth, Actias
4. **Performance**: Live quantum state manipulation

## History

| Year | Milestone |
|------|-----------|
| 2022 | First quantum-composed music (Ludovico Quanthoven) |
| 2022 | Miranda's "Quantum Computer Music" book |
| 2023 | Q1Synth (Miranda, Thomas, Itaboraí) |
| 2024 | Quantum Guitar debuts (Edinburgh) |
| 2024 | Black Tish at Wacken with quantum |
| 2025 | "Bell" composition (ZX notation) |

## Compositional Approaches

### 1. Quantum Random (QRandom)

```python
from qiskit import QuantumCircuit, execute, Aer

def quantum_melody(n_notes, n_pitches=12):
    """Generate melody via quantum measurement."""
    qc = QuantumCircuit(4, 4)
    qc.h(range(4))  # Superposition
    qc.measure(range(4), range(4))
    
    backend = Aer.get_backend('qasm_simulator')
    result = execute(qc, backend, shots=n_notes).result()
    
    melody = []
    for bitstring, count in result.get_counts().items():
        pitch = int(bitstring, 2) % n_pitches
        melody.extend([pitch] * count)
    
    return melody
```

### 2. Quantum Walk Composition

```python
def quantum_walk_melody(graph, steps):
    """Melody from quantum walk on graph."""
    from discopy.quantum import qubit, H, CNOT
    
    # Initialize walker in superposition
    walker = uniform_superposition(len(graph.nodes))
    
    for _ in range(steps):
        # Coin flip
        walker = apply_coin(walker)
        # Shift
        walker = apply_shift(walker, graph)
    
    # Measure to get note sequence
    return measure_melody(walker)
```

### 3. Grover Search for Harmony

```python
def find_chord(target_quality='major'):
    """Use Grover to find ch