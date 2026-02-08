---
name: catcolab-stock-flow
description: CatColab Stock-and-Flow Diagrams - epidemiological and ecological modeling with stocks (accumulations), flows (rates), and mass-action ODE semantics for SIR models and population dynamics.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# CatColab Stock-and-Flow Diagrams: Epidemiology & Ecology

**Trit**: +1 (PLUS - generator)
**Color**: Orange (#FF8C00)

## Overview

Stock-and-Flow diagrams in CatColab model systems with:
- **Stocks**: Accumulations (populations, inventories, quantities)
- **Flows**: Rates of change between stocks
- **Links**: Auxiliary connections influencing flow rates
- **Mass-action semantics**: Automatic ODE generation

This is the foundation for epidemiological models (SIR), ecological models (Lotka-Volterra), and resource dynamics.

## Mathematical Foundation

```
┌─────────────────────────────────────────────────────┐
│           STOCK-AND-FLOW DIAGRAM                     │
├─────────────────────────────────────────────────────┤
│  Stocks (Accumulations):                             │
│    [S] Susceptible  [I] Infected  [R] Recovered      │
│                                                      │
│  Flows (Rates):                                      │
│    infection: S → I                                  │
│    recovery: I → R                                   │
│                                                      │
│  Links (Influences):                                 │
│    I ──link──► infection (infected influence rate)   │
│                                                      │
│  Diagram:                                            │
│    ┌───┐  infection  ┌───┐  recovery  ┌───┐         │
│    │ S │ ═══════════► │ I │ ═══════════► │ R │         │
│    └───┘             └───┘             └───┘         │
│      ▲                 │                             │
│      └────── link ─────┘                             │
└─────────────────────────────────────────────────────┘
```

## Double Theory

```rust
// Stock-Flow double theory
pub fn th_stock_flow() -> DiscreteDblTheory {
    let mut cat = FpCategory::new();

    // Object type
    cat.add_ob_generator(name("Stock"));

    // Morphism types
    cat.add_mor_generator(name("Flow"), name("Stock"), name("Stock"));
  