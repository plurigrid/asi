---
name: catcolab-regulatory-networks
description: CatColab Regulatory Networks - signed graphs for molecular biology modeling gene regulatory networks with positive (activating) and negative (inhibiting) edges.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
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

    // Constraint: n ⊙ n = id (dou