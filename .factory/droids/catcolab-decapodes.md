---
name: catcolab-decapodes
description: CatColab Decapodes - Discrete Exterior Calculus for PDE modeling on meshes via Decapodes.jl integration. Model physics equations compositionally with automatic code generation.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# CatColab Decapodes: Discrete Exterior Calculus

**Trit**: -1 (MINUS - validator/verifier)
**Color**: Purple (#8A2BE2)

## Overview

Decapodes in CatColab enable **Discrete Exterior Calculus (DEC)** for modeling PDEs:
- **Differential forms**: 0-forms (scalars), 1-forms (vectors), 2-forms (flux)
- **Operators**: d (exterior derivative), ★ (Hodge star), Δ (Laplacian)
- **Multiphysics**: Compose PDEs from different domains
- **Automatic code generation**: Export to AlgebraicJulia/Decapodes.jl

This is CatColab's most advanced logic, connecting category theory to numerical PDE simulation.

## Mathematical Foundation

Discrete Exterior Calculus discretizes differential geometry on meshes:

```
┌─────────────────────────────────────────────────────┐
│              DISCRETE EXTERIOR CALCULUS              │
├─────────────────────────────────────────────────────┤
│  Spaces (Differential Forms):                        │
│    Ω⁰ (0-forms): Scalars on vertices (temperature)  │
│    Ω¹ (1-forms): Vectors on edges (velocity)        │
│    Ω² (2-forms): Flux through faces (flow rate)     │
│                                                      │
│  Operators:                                          │
│    d: Ωᵏ → Ωᵏ⁺¹  (exterior derivative)              │
│    ★: Ωᵏ → Ωⁿ⁻ᵏ  (Hodge star)                       │
│    δ = ★d★: Ωᵏ → Ωᵏ⁻¹ (codifferential)              │
│    Δ = dδ + δd: Laplacian                           │
│                                                      │
│  De Rham Complex:                                    │
│    Ω⁰ ──d──► Ω¹ ──d──► Ω² ──d──► Ω³                 │
│     │         │         │         │                  │
│     ★         ★         ★         ★                  │
│     ▼         ▼         ▼         ▼                  │
│    Ω³ ◄──d── Ω² ◄──d── Ω¹ ◄──d── Ω⁰                 │
└─────────────────────────────────────────────────────┘
```

## Double Theory

```rust
// DEC double theory (simplified)
pub fn th_decapodes() -> DiscreteDblTheory {
    l