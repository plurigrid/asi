---
name: catcolab-regulatory-networks
description: CatColab Regulatory Networks - signed graphs for molecular biology modeling gene regulatory networks with positive (activating) and negative (inhibiting) edges.
version: 1.0.0
---

# CatColab Regulatory Networks: Molecular Biology Modeling

**Trit**: -1 (MINUS - validator/inhibitor)
**Color**: Red (#DC143C)

## Overview

Regulatory Networks in CatColab model molecular interactions that control gene expression:
- **Nodes**: Genes, proteins, RNA, metabolites
- **Positive edges**: Activation/promotion (+)
- **Negative edges**: Inhibition/repression (-)

These signed graphs capture the control logic of biological systems.

## Mathematical Foundation

A regulatory network is a **signed graph** or **signed category**:

```
┌─────────────────────────────────────────────────────┐
│              REGULATORY NETWORK                      │
├─────────────────────────────────────────────────────┤
│  Nodes (Genes/Proteins):                             │
│    GeneA, GeneB, GeneC, ProteinX                     │
│                                                      │
│  Positive Edges (Activation):                        │
│    GeneA ──(+)──► GeneB                              │
│    ProteinX ──(+)──► GeneC                           │
│                                                      │
│  Negative Edges (Inhibition):                        │
│    GeneB ──(-)──► GeneC                              │
│    GeneC ──(-)──► GeneA  (negative feedback)         │
│                                                      │
│  Motifs:                                             │
│    Feedforward loop: A→B→C, A→C                      │
│    Negative feedback: A→B→C⊣A                        │
└─────────────────────────────────────────────────────┘
```

## Double Theory

```rust
// Signed category double theory
pub fn th_signed_category() -> DiscreteDblTheory {
    let mut cat = FpCategory::new();

    // Object type
    cat.add_ob_generator(name("Node"));

    // Morphism types (signed edges)
    cat.add_mor_generator(name("Positive"), name("Node"), name("Node"));
    cat.add_mor_generator(name("Negative"), name("Node"), name("Node"));

    // Constraint: n ⊙ n = id (double negative = positive)
    cat.add_equation(
        compose(name("Negative"), name("Negative")),
        identity(name("Node"))
    );

    cat.into()
}
```

## CatColab Implementation

### Node Declaration

```typescript
{
  "type": "ObDecl",
  "name": "p53",
  "theory_type": "Node",
  "description": "tumor suppressor protein"
}
```

### Positive Regulation (Activation)

```typescript
{
  "type": "MorDecl",
  "name": "activates_apoptosis",
  "dom": "p53",
  "cod": "Bax",
  "theory_type": "Positive",
  "description": "p53 promotes apoptosis via Bax"
}
```

### Negative Regulation (Inhibition)

```typescript
{
  "type": "MorDecl",
  "name": "inhibits_growth",
  "dom": "p53",
  "cod": "CyclinD",
  "theory_type": "Negative",
  "description": "p53 blocks cell cycle progression"
}
```

## Network Motifs

### Feedforward Loop (FFL)

```
     GeneA
    /     \
   +       +
  ↓         ↓
GeneB ──+──► GeneC

Type: Coherent (all positive)
Function: Noise filtering, delay
```

### Negative Feedback Loop

```
GeneA ──+──► GeneB ──+──► GeneC
  ▲                        │
  └────────(-)─────────────┘

Function: Homeostasis, oscillation
```

### Toggle Switch (Bistability)

```
GeneA ◄──(-)──► GeneB
         ⇅
       (-)

Function: Binary cell fate decision
```

## Practical Examples

### Example 1: p53 Tumor Suppressor Network

```
Nodes: p53, MDM2, ATM, Bax, p21

Edges:
  ATM ──(+)──► p53       (DNA damage activates p53)
  p53 ──(+)──► MDM2      (p53 induces its own inhibitor)
  MDM2 ──(-)──► p53      (MDM2 degrades p53)
  p53 ──(+)──► Bax       (p53 promotes apoptosis)
  p53 ──(+)──► p21       (p53 arrests cell cycle)

Motif: p53-MDM2 negative feedback loop
```

### Example 2: Lac Operon

```
Nodes: LacI, LacZ, Lactose, Glucose

Edges:
  LacI ──(-)──► LacZ     (repressor blocks transcription)
  Lactose ──(-)──► LacI  (lactose inactivates repressor)
  Glucose ──(-)──► LacZ  (catabolite repression)

Function: Metabolic switch for sugar utilization
```

## Analysis Capabilities

CatColab can analyze regulatory networks for:
- **Steady states**: Fixed points of the dynamics
- **Stability**: Eigenvalue analysis of Jacobian
- **Motif enrichment**: Statistical over-representation
- **Boolean dynamics**: Logical model simulation

## GF(3) Triads

```
catcolab-regulatory-networks (-1) ⊗ topos-catcolab (0) ⊗ catcolab-stock-flow (+1) = 0 ✓
crn-topology (-1) ⊗ catcolab-regulatory-networks (0) ⊗ alife (+1) = 0 ✓
```

## Commands

```bash
# Create regulatory network
just catcolab-new regulatory "p53-network"

# Analyze motifs
just catcolab-analyze p53-network --motifs

# Export to SBML
just catcolab-export p53-network --format=sbml

# Simulate Boolean dynamics
just catcolab-simulate p53-network --boolean
```

## References

- Alon (2007) "Network motifs: theory and experimental approaches"
- Karlebach & Shamir (2008) "Modelling and analysis of gene regulatory networks"
- [CatColab Regulatory Networks Help](https://catcolab.org/help/logics/regulatory)

---

**Skill Name**: catcolab-regulatory-networks
**Type**: Systems Biology / Gene Regulation
**Trit**: -1 (MINUS)
**GF(3)**: Conserved via triadic composition
