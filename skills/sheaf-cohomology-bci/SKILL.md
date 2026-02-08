---
name: sheaf-cohomology-bci
description: Local-to-global signal consistency via cellular sheaves, Cech cohomology, and sheaf Laplacian
version: 1.0.0
---

# Sheaf Cohomology BCI Skill: Local-to-Global Consistency

**Status**: Production Ready
**Trit**: -1 (MINUS - validator)
**Color**: #2626D8 (Blue)
**Principle**: Sheaf condition = local-to-global consistency principle
**Frame**: Cellular sheaf on BCI signal graph with Cech cohomology

---

## Overview

**Sheaf Cohomology** verifies that local BCI measurements (per channel) can be consistently glued into a global signal. Implements:

1. **Cellular sheaf**: Stalks F(v) at vertices, restriction maps on edges
2. **Sheaf condition**: Gluing axiom verification across overlapping regions
3. **Cech cohomology**: H^0 (global sections), H^1 (obstructions to gluing)
4. **Sheaf Laplacian**: Tr(L_F) measures total inconsistency
5. **Descent/gluing**: Attempt global section construction, identify obstruction class

**Correct by construction**: H^1 = 0 iff local sections glue uniquely to global.

## Core Formulae

```
Cellular sheaf F on graph G = (V, E):
  F(v) = stalk (vector space) at vertex v
  rho_{v,e}: F(v) -> F(e)  restriction map

Sheaf condition:
  rho_{u,e}(s_u) = rho_{v,e}(s_v) for all edges e=(u,v)

Cech cohomology:
  C^0 = prod F(U_i)           (local sections)
  C^1 = prod F(U_i cap U_j)   (overlap data)
  delta_0: C^0 -> C^1          (coboundary)
  H^0 = ker(delta_0)           (global sections)
  H^1 = ker(delta_1)/im(delta_0)  (obstructions)

Sheaf Laplacian:
  L_F = delta^T delta
  Tr(L_F) = total inconsistency
  ker(L_F) = harmonic sections (global)
```

## Key Results

```
Multi-World Sheaf Comparison:
  world-a: Tr(L_F)=3.24, non-trivial obstruction (beta-gamma disagreement)
  world-b: Tr(L_F)=0.09, GLUED (consistent signals, trivial H^1)
  world-c: Tr(L_F)=20.75, highly inconsistent (diverse channels)
```

## BCI Integration (Layer 19)

Completes the **Topology Chain**: L8 -> L13 -> L14 -> L17 -> L19

- **L8 Persistent Homology**: Betti = ranks of constant sheaf cohomology
- **L14 Cohomology Ring**: Sheaf H^k(X,F) generalizes H^k(X,Z)
- **L17 de Rham**: de Rham = cohomology of sheaf of smooth functions
- **L18 Info Geometry**: Sheaf of distributions, Fisher metric varies by stalk
- **L16 Spectral**: Sheaf Laplacian L_F generalizes graph Laplacian L

---

**Skill Name**: sheaf-cohomology-bci
**Type**: Local-to-Global Consistency / Cellular Sheaves / Cech Cohomology
**Trit**: -1 (MINUS)
**GF(3)**: Forms valid triads with ERGODIC + PLUS skills

## Integration with GF(3) Triads

```
stochastic-resonance (+1) x information-geometry (0) x sheaf-cohomology-bci (-1) = 0
gay-mcp (+1) x spectral-methods (0) x sheaf-cohomology-bci (-1) = 0
```
