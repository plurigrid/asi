---
name: assembly-index
description: Lee Cronin's Assembly Theory for molecular complexity measurement and
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Assembly Index Skill: Molecular Complexity Validation

**Status**: ✅ Production Ready
**Trit**: -1 (MINUS - validator/constraint)
**Color**: #2626D8 (Blue)
**Principle**: Complexity threshold → Life signature
**Frame**: Assembly pathways with minimal step counting

---

## Overview

**Assembly Index** measures molecular complexity by counting the minimum number of joining operations needed to construct a molecule from basic building blocks. Molecules with assembly index > 15 are biosignatures—too complex for random chemistry.

1. **Assembly pathway**: Shortest construction sequence
2. **Copy number threshold**: Abundance × complexity = life signal
3. **Molecular DAG**: Directed acyclic graph of substructures
4. **Mass spectrometry integration**: MA(m/z) measurement

## Core Formula

```
MA(molecule) = min |steps| to construct from primitives
Life threshold: MA > 15 with copy_number > 1
```

```python
def assembly_index(molecule: Molecule) -> int:
    """Compute minimum assembly steps via dynamic programming."""
    substructures = enumerate_substructures(molecule)
    dag = build_assembly_dag(substructures)
    return shortest_path_length(dag, source="primitives", target=molecule)
```

## Key Concepts

### 1. Assembly Pathway Enumeration

```python
class AssemblyPathway:
    def __init__(self, molecule):
        self.mol = molecule
        self.fragments = self.decompose()
    
    def decompose(self) -> list[Fragment]:
        """Find all valid bond-breaking decompositions."""
        return [split for split in self.mol.bonds 
                if split.yields_valid_fragments()]
    
    def minimal_pathway(self) -> list[JoinOperation]:
        """DP over fragment DAG for minimum steps."""
        memo = {}
        return self._dp_assemble(self.mol, memo)
```

### 2. Copy Number Amplification

```python
def is_biosignature(molecule, sample) -> bool:
    ma = assembly_index(molecule)
    copies = sample.count(molecule)
    # Life creates copies of complex molecules
