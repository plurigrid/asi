---
name: crn-topology
description: Chemical Reaction Network topology for generating and analyzing reaction graph structures.
source: local
license: UNLICENSED
---

# CRN Topology Skill: Reaction Network Generation

**Status**: ✅ Production Ready
**Trit**: +1 (PLUS - generator)
**Color**: #D82626 (Red)
**Principle**: Network structure → Dynamical behavior
**Frame**: Hypergraph topology of chemical reactions

---

## Overview

**CRN Topology** generates and analyzes the graph structure of chemical reaction networks. The topology determines qualitative dynamics—multistability, oscillations, and computational capacity.

1. **Species-reaction graph**: Bipartite hypergraph
2. **Stoichiometric matrix**: Linear algebra of reactions
3. **Deficiency**: Gap between complexes and rank
4. **Persistence**: Network admits no extinctions

## Core Formula

```
Deficiency δ = n - ℓ - s
  n = number of complexes
  ℓ = number of linkage classes  
  s = rank of stoichiometric matrix

Zero deficiency theorem:
  δ = 0 and weakly reversible ⟹ unique stable equilibrium
```

```python
def crn_deficiency(network: CRN) -> int:
    n = len(network.complexes)
    l = network.linkage_classes()
    s = np.linalg.matrix_rank(network.stoichiometry)
    return n - l - s
```

## Key Concepts

### 1. Stoichiometric Matrix Generation

```python
class CRNGenerator:
    def __init__(self, species: list[str]):
        self.species = species
    
    def random_reaction(self) -> Reaction:
        """Generate topology-valid reaction."""
        reactants = self.sample_complex()
        products = self.sample_complex()
        return Reaction(reactants, products)
    
    def stoichiometry_matrix(self, reactions) -> np.ndarray:
        """S[i,j] = net change in species i from reaction j."""
        S = np.zeros((len(self.species), len(reactions)))
        for j, rxn in enumerate(reactions):
            S[:, j] = rxn.products - rxn.reactants
        return S
```

### 2. Network Motif Generation

```python
def generate_oscillator_topology() -> CRN:
    """Generate Brusselator-like topology."""
    return CRN([
        "A → X",
        "2X + Y → 3X",
        "B + X → Y + D", 
        "X → E"
    ])

def generate_bistable_topology() -> CRN:
    """Generate Schlögl-like bistability."""
    return CRN([
        "A + 2X ⇌ 3X",
        "X ⇌ B"
    ])
```

### 3. Deficiency Analysis

```python
def analyze_topology(crn: CRN) -> dict:
    """Determine dynamical properties from topology."""
    delta = crn_deficiency(crn)
    wr = is_weakly_reversible(crn)
    return {
        "deficiency": delta,
        "weakly_reversible": wr,
        "unique_equilibrium": delta == 0 and wr,
        "multistability_possible": delta > 0,
        "complex_balanced": check_complex_balance(crn)
    }
```

## Commands

```bash
# Generate CRN with target properties
just crn-generate --oscillator --species 3

# Compute deficiency
just crn-deficiency network.crn

# Visualize reaction hypergraph
just crn-topology network.crn
```

## Integration with GF(3) Triads

```
assembly-index (-1) ⊗ turing-chemputer (0) ⊗ crn-topology (+1) = 0 ✓  [Molecular Complexity]
persistent-homology (-1) ⊗ turing-chemputer (0) ⊗ crn-topology (+1) = 0 ✓  [Topological CRN]
```

## Related Skills

- **turing-chemputer** (0): Execute reactions in CRN
- **assembly-index** (-1): Validate molecular complexity
- **acsets** (0): Algebraic representation of CRN hypergraph

---

**Skill Name**: crn-topology
**Type**: Reaction Network Generator
**Trit**: +1 (PLUS)
**Color**: #D82626 (Red)
