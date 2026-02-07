# CatColab-Regulatory-Networks Neighbor Skills

**Date**: 2026-01-19
**Trit**: -1 (MINUS - validator/inhibitor)
**Role**: Signed graphs for molecular biology gene regulation

---

## Core Triad

| Skill | Trit | Interface |
|-------|------|-----------|
| **catcolab-regulatory-networks** | -1 | Network validation |
| **catcolab-causal-loop** | 0 | Feedback coordination |
| **catcolab-stock-flow** | +1 | Population dynamics |

**GF(3)**: (-1) + (0) + (+1) = 0 ✓

---

## Immediate Neighbors

### catcolab-causal-loop (0)
**Morphism**: Regulatory → Causal loop (equivalent)
```
Regulatory Network ≅ Causal Loop Diagram
  Positive edge (+) ≅ Positive link
  Negative edge (-) ≅ Negative link
  Gene → Variable
```

### catcolab-stock-flow (+1)
**Morphism**: Network → Dynamical system
```julia
# Regulatory network induces stock-flow dynamics
# Activation: dB/dt = +f(A)
# Inhibition: dB/dt = -g(A)
```

### crn-topology (-1)
**Morphism**: Regulatory → Chemical reaction network
```
Regulatory network → CRN
  A ──(+)──► B  →  A → A + B (production)
  A ──(-)──► B  →  A + B → A (degradation)
```

### alife (+1)
**Morphism**: Network → Artificial life dynamics
```python
# Gene regulatory network drives cell behavior
def cell_update(network, state):
    for gene, regulators in network.items():
        state[gene] = boolean_function(regulators, state)
```

### topos-catcolab (0)
**Morphism**: Network → CatColab model
```typescript
const network = catcolab.createModel("regulatory", "p53-network");
network.addNode("p53");
network.addNode("MDM2");
network.addPositive("p53", "MDM2");  // p53 activates MDM2
network.addNegative("MDM2", "p53");  // MDM2 inhibits p53
```

---

## Neighbor Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Biology | catcolab-regulatory-networks ⊗ catcolab-stock-flow ⊗ alife | Gene → Population → Life |
| Systems | catcolab-regulatory-networks ⊗ catcolab-causal-loop ⊗ dynamical-system-functor | Network → Feedback → Dynamics |
| Chemistry | crn-topology ⊗ catcolab-regulatory-networks ⊗ assembly-index | CRN → Gene → Complexity |
