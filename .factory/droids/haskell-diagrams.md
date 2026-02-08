---
name: haskell-diagrams
description: haskell-diagrams - Declarative Vector Graphics with Diagrams DSL
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# haskell-diagrams - Declarative Vector Graphics with Diagrams DSL

## Overview

Integrates the Haskell [diagrams](https://hackage.haskell.org/package/diagrams) embedded domain-specific language for creating declarative vector graphics. Used for:

1. **Tsillerson Automata Visualization**: 2+1D lattice with vortex/antivortex defects
2. **Golden Thread Color Spirals**: φ-angle (137.508°) color progression
3. **Path Equivalence Diagrams**: Kleppmann-Bumpus-Gay path comparison
4. **GF(3) Trit Coloring**: Triadic conservation visualizations

**Trit**: +1 (PLUS) - Generates vector graphics artifacts

## Core Formula

```haskell
-- Diagrams is a monoid: composition via <>
diagram :: Diagram B
diagram = shape1 <> shape2 `atop` shape3

-- Transformation pipeline
transform :: Diagram B -> Diagram B
transform = scale 2 . rotate (45 @@ deg) . fc red
```

## Predicates

| Predicate | Description | GF(3) Role |
|-----------|-------------|------------|
| `DiagramValid(d)` | Diagram is well-formed | Structure |
| `ColorConserved(ds)` | Σ trits = 0 across diagrams | Conservation |
| `PathEquivalent(p1,p2)` | Visual fingerprints match | Equivalence |
| `GoldenAngle(θ)` | θ ≈ 137.508° | Dispersion |

## Architecture

```
┌────────────────────────────────────────────────────────────────┐
│                  Haskell Diagrams Pipeline                     │
├────────────────────────────────────────────────────────────────┤
│                                                                 │
│   Source (.hs)          Diagram B              Output           │
│       │                     │                     │             │
│       ▼                     ▼                     ▼             │
│  ┌──────────┐    ┌───────────────────┐    ┌─────────────┐      │
│  │ DSL Code │───▶│  Monoid Compose   │───▶│ SVG / PNG   │      │
│  │ shapes,  │    │  atop, beside,    │    │ PDF / PS    │      │
│  │ colors   │    │  vsep, hsep       │    │ Canvas      │      │
│  └──────────┘    └─────────────────